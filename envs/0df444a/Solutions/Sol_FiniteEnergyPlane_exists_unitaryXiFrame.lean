-- Prove2me | solution 1 for FiniteEnergyPlane.exists_unitaryXiFrame
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:19:15.097042+00:00
-- url     : https://prove2.me/submissions/5588f5cf-4bbf-44ad-a563-7c41be43feaf

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_reeb_spec

set_option linter.all false

open Module

namespace UFrame

section abstract
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (g : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (J A B : E →ₗ[ℝ] E)

/-- Hermitian-type data on a subspace `W`: `g` an inner product on `W`, `J` an orthogonal complex
structure, `A` an operator commuting with `J` with `g`-adjoint `B`. -/
structure Good (W : Submodule ℝ E) : Prop where
  symm : ∀ u ∈ W, ∀ v ∈ W, g u v = g v u
  pos : ∀ u ∈ W, u ≠ 0 → 0 < g u u
  JW : ∀ u ∈ W, J u ∈ W
  JJ : ∀ u ∈ W, J (J u) = -u
  gJ : ∀ u ∈ W, ∀ v ∈ W, g (J u) (J v) = g u v
  AW : ∀ u ∈ W, A u ∈ W
  BW : ∀ u ∈ W, B u ∈ W
  adj : ∀ u ∈ W, ∀ v ∈ W, g (A u) v = g u (B v)
  AJ : ∀ u ∈ W, A (J u) = J (A u)
  BJ : ∀ u ∈ W, B (J u) = J (B u)

/-- every nonzero invariant subspace contains a unit "complex eigenvector" -/
def Oracle (W : Submodule ℝ E) : Prop :=
  ∀ W' ≤ W, (∀ u ∈ W', J u ∈ W') → (∀ u ∈ W', A u ∈ W') → (∀ u ∈ W', B u ∈ W') → W' ≠ ⊥ →
    ∃ e ∈ W', g e e = 1 ∧ ∃ θ : ℝ, A e = Real.cos θ • e + Real.sin θ • J e ∧
      B e = Real.cos θ • e - Real.sin θ • J e

variable {g J A B}

lemma Good.skew {W : Submodule ℝ E} (hW : Good g J A B W) {u v : E} (hu : u ∈ W) (hv : v ∈ W) :
    g (J u) v = - g u (J v) := by
  have := hW.gJ (J u) (hW.JW u hu) v hv
  rw [hW.JJ u hu] at this
  rw [← this]; simp

lemma Good.mono {W W' : Submodule ℝ E} (hW : Good g J A B W) (hle : W' ≤ W)
    (hJ : ∀ u ∈ W', J u ∈ W') (hA : ∀ u ∈ W', A u ∈ W') (hB : ∀ u ∈ W', B u ∈ W') :
    Good g J A B W' where
  symm u hu v hv := hW.symm u (hle hu) v (hle hv)
  pos u hu := hW.pos u (hle hu)
  JW := hJ
  JJ u hu := hW.JJ u (hle hu)
  gJ u hu v hv := hW.gJ u (hle hu) v (hle hv)
  AW := hA
  BW := hB
  adj u hu v hv := hW.adj u (hle hu) v (hle hv)
  AJ u hu := hW.AJ u (hle hu)
  BJ u hu := hW.BJ u (hle hu)

theorem nf (W : Submodule ℝ E) (hW : Good g J A B W) (hO : Oracle g J A B W) :
    ∃ m : ℕ, ∃ e : Fin m → E, ∃ θ : Fin m → ℝ, (∀ k, e k ∈ W) ∧
      (∀ i j, g (e i) (e j) = if i = j then 1 else 0) ∧ (∀ i j, g (e i) (J (e j)) = 0) ∧
      (∀ k, A (e k) = Real.cos (θ k) • e k + Real.sin (θ k) • J (e k)) ∧
      (∀ w ∈ W, w = ∑ k, (g w (e k) • e k + g w (J (e k)) • J (e k))) := by
  induction hr : finrank ℝ W using Nat.strong_induction_on generalizing W with
  | _ r ih =>
  by_cases hbot : W = ⊥
  · subst hbot
    refine ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, fun i => i.elim0, fun i => i.elim0,
      fun k => k.elim0, ?_⟩
    intro w hw
    rw [Submodule.mem_bot] at hw
    simp [hw]
  obtain ⟨e0, he0W, he0, θ0, hA0, hB0⟩ := hO W le_rfl hW.JW hW.AW hW.BW hbot
  have hJe0W : J e0 ∈ W := hW.JW e0 he0W
  have h01 : g e0 (J e0) = 0 := by
    have h1 := hW.skew he0W he0W
    have h2 := hW.symm (J e0) hJe0W e0 he0W
    linarith
  have h10 : g (J e0) e0 = 0 := by rw [hW.symm _ hJe0W _ he0W, h01]
  have h11 : g (J e0) (J e0) = 1 := by rw [hW.gJ _ he0W _ he0W, he0]
  let W' : Submodule ℝ E := W ⊓ (LinearMap.ker (g.flip e0) ⊓ LinearMap.ker (g.flip (J e0)))
  have mem' : ∀ u, u ∈ W' ↔ u ∈ W ∧ g u e0 = 0 ∧ g u (J e0) = 0 := by
    intro u; simp [W', LinearMap.flip_apply]
  have hle : W' ≤ W := inf_le_left
  have hJ' : ∀ u ∈ W', J u ∈ W' := by
    intro u hu
    obtain ⟨huW, hu1, hu2⟩ := (mem' u).1 hu
    refine (mem' _).2 ⟨hW.JW u huW, ?_, ?_⟩
    · rw [hW.skew huW he0W, hu2, neg_zero]
    · rw [hW.gJ u huW e0 he0W, hu1]
  have hA' : ∀ u ∈ W', A u ∈ W' := by
    intro u hu
    obtain ⟨huW, hu1, hu2⟩ := (mem' u).1 hu
    refine (mem' _).2 ⟨hW.AW u huW, ?_, ?_⟩
    · rw [hW.adj u huW e0 he0W, hB0]; simp [hu1, hu2]
    · rw [hW.adj u huW _ hJe0W, hW.BJ e0 he0W, hB0, map_sub, map_smul, map_smul,
        hW.JJ e0 he0W]
      simp [hu1, hu2]
  have hB' : ∀ u ∈ W', B u ∈ W' := by
    intro u hu
    obtain ⟨huW, hu1, hu2⟩ := (mem' u).1 hu
    have hu1' : g e0 u = 0 := by rw [hW.symm _ he0W _ huW, hu1]
    have hu2' : g (J e0) u = 0 := by rw [hW.symm _ hJe0W _ huW, hu2]
    refine (mem' _).2 ⟨hW.BW u huW, ?_, ?_⟩
    · rw [hW.symm _ (hW.BW u huW) _ he0W, ← hW.adj e0 he0W u huW, hA0]; simp [hu1', hu2']
    · rw [hW.symm _ (hW.BW u huW) _ hJe0W, ← hW.adj _ hJe0W u huW, hW.AJ e0 he0W, hA0,
        map_add, map_smul, map_smul, hW.JJ e0 he0W]
      simp [hu1', hu2']
  have hW' : Good g J A B W' := hW.mono hle hJ' hA' hB'
  have hO' : Oracle g J A B W' := fun W'' h'' => hO W'' (h''.trans hle)
  have hlt : W' < W := by
    refine lt_of_le_of_ne hle fun h => ?_
    have : e0 ∈ W' := h ▸ he0W
    have := ((mem' e0).1 this).2.1
    rw [he0] at this; exact one_ne_zero this
  have hrk : finrank ℝ W' < r := hr ▸ Submodule.finrank_lt_finrank_of_lt hlt
  obtain ⟨m, e, θ, heW, hee, heJ, hAe, hspan⟩ := ih _ hrk W' hW' hO' rfl
  have he_0 : ∀ k, g (e k) e0 = 0 := fun k => ((mem' _).1 (heW k)).2.1
  have he_1 : ∀ k, g (e k) (J e0) = 0 := fun k => ((mem' _).1 (heW k)).2.2
  have h0_e : ∀ k, g e0 (e k) = 0 := fun k => by rw [hW.symm _ he0W _ (hle (heW k)), he_0]
  have h0_Je : ∀ k, g e0 (J (e k)) = 0 := fun k => by
    rw [hW.symm _ he0W _ (hle (hJ' _ (heW k)))]; exact ((mem' _).1 (hJ' _ (heW k))).2.1
  have h1_e : ∀ k, g (J e0) (e k) = 0 := fun k => by
    rw [hW.symm _ hJe0W _ (hle (heW k)), he_1]
  have h1_Je : ∀ k, g (J e0) (J (e k)) = 0 := fun k => by
    rw [hW.gJ _ he0W _ (hle (heW k)), h0_e]
  refine ⟨m + 1, Fin.cons e0 e, Fin.cons θ0 θ, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa using he0W
    · simpa using hle (heW k)
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [he0]
    · simp [h0_e, (Fin.succ_ne_zero j).symm]
    · simp [he_0, Fin.succ_ne_zero i]
    · simp [hee, Fin.succ_inj]
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [h01]
    · simp [h0_Je]
    · simp [he_1]
    · simp [heJ]
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa using hA0
    · simpa using hAe k
  · intro w hw
    set w' := w - g w e0 • e0 - g w (J e0) • J e0 with hw'def
    have hw'W : w' ∈ W' := by
      refine (mem' _).2 ⟨?_, ?_, ?_⟩
      · exact W.sub_mem (W.sub_mem hw (W.smul_mem _ he0W)) (W.smul_mem _ hJe0W)
      · simp [w', he0, h10]
      · simp [w', h01, h11]
    have hs := hspan w' hw'W
    have c1 : ∀ k, g w' (e k) = g w (e k) := fun k => by simp [w', h0_e, h1_e]
    have c2 : ∀ k, g w' (J (e k)) = g w (J (e k)) := fun k => by simp [w', h0_Je, h1_Je]
    simp only [c1, c2] at hs
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hs, hw'def]
    abel


/-! ### Frames built from a `J`-orthonormal family -/

variable (J) in
/-- `a ↦ ∑ₖ a(inl k) eₖ + a(inr k) J eₖ` -/
noncomputable def frameL {m : ℕ} (e : Fin m → E) : EuclideanSpace ℝ (Fin m ⊕ Fin m) →ₗ[ℝ] E where
  toFun a := ∑ k, (a (Sum.inl k) • e k + a (Sum.inr k) • J (e k))
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]; abel
  map_smul' c a := by simp [Finset.smul_sum, smul_smul]

variable (g J) in
noncomputable def coordL {m : ℕ} (e : Fin m → E) : E →ₗ[ℝ] EuclideanSpace ℝ (Fin m ⊕ Fin m) where
  toFun w := WithLp.toLp 2 (Sum.elim (fun k => g w (e k)) (fun k => g w (J (e k))))
  map_add' a b := by ext i; cases i <;> simp
  map_smul' c a := by ext i; cases i <;> simp

lemma frameL_apply {m : ℕ} (e : Fin m → E) (a : EuclideanSpace ℝ (Fin m ⊕ Fin m)) :
    frameL J e a = ∑ k, (a (Sum.inl k) • e k + a (Sum.inr k) • J (e k)) := rfl

@[simp] lemma coordL_inl {m : ℕ} (e : Fin m → E) (w : E) (k : Fin m) :
    coordL g J e w (Sum.inl k) = g w (e k) := rfl
@[simp] lemma coordL_inr {m : ℕ} (e : Fin m → E) (w : E) (k : Fin m) :
    coordL g J e w (Sum.inr k) = g w (J (e k)) := rfl

end abstract

/-! ### The standard complex structure on `ℝ^{2m}` -/

noncomputable abbrev Jv (m : ℕ) :
    EuclideanSpace ℝ (Fin m ⊕ Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m ⊕ Fin m) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.J (Fin m) ℝ))

lemma Jv_inl {m : ℕ} (a : EuclideanSpace ℝ (Fin m ⊕ Fin m)) (k : Fin m) :
    Jv m a (Sum.inl k) = - a (Sum.inr k) := by
  simp [Matrix.J, Matrix.toEuclideanLin_apply, Matrix.mulVec, Matrix.fromBlocks, dotProduct,
    Fintype.sum_sum_type, Matrix.one_apply]

lemma Jv_inr {m : ℕ} (a : EuclideanSpace ℝ (Fin m ⊕ Fin m)) (k : Fin m) :
    Jv m a (Sum.inr k) = a (Sum.inl k) := by
  simp [Matrix.J, Matrix.toEuclideanLin_apply, Matrix.mulVec, Matrix.fromBlocks, dotProduct,
    Fintype.sum_sum_type, Matrix.one_apply]

lemma inner_eq_sum {m : ℕ} (a b : EuclideanSpace ℝ (Fin m ⊕ Fin m)) :
    inner ℝ a b = ∑ k, (a (Sum.inl k) * b (Sum.inl k) + a (Sum.inr k) * b (Sum.inr k)) := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, Finset.sum_add_distrib, mul_comm]

lemma Jv_Jv {m : ℕ} (a : EuclideanSpace ℝ (Fin m ⊕ Fin m)) : Jv m (Jv m a) = -a := by
  ext i; cases i with
  | inl k => rw [Jv_inl, Jv_inr]; simp
  | inr k => rw [Jv_inr, Jv_inl]; simp

lemma inner_Jv {m : ℕ} (a b : EuclideanSpace ℝ (Fin m ⊕ Fin m)) :
    inner ℝ (Jv m a) b = - inner ℝ a (Jv m b) := by
  simp only [inner_eq_sum, Jv_inl, Jv_inr, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma inner_Jv_Jv {m : ℕ} (a b : EuclideanSpace ℝ (Fin m ⊕ Fin m)) :
    inner ℝ (Jv m a) (Jv m b) = inner ℝ a b := by
  rw [inner_Jv, Jv_Jv, inner_neg_right, neg_neg]

section abstract2
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {g : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} {J A B : E →ₗ[ℝ] E} {W : Submodule ℝ E} (hW : Good g J A B W)
  {m : ℕ} {e : Fin m → E} (heW : ∀ k, e k ∈ W)
  (hee : ∀ i j, g (e i) (e j) = if i = j then 1 else 0) (heJ : ∀ i j, g (e i) (J (e j)) = 0)
include hW heW hee heJ

lemma frame_mem (a : EuclideanSpace ℝ (Fin m ⊕ Fin m)) : frameL J e a ∈ W := by
  rw [frameL_apply]; exact W.sum_mem fun k _ => W.add_mem (W.smul_mem _ (heW k)) (W.smul_mem _ (hW.JW _ (heW k)))

lemma frame_J (a : EuclideanSpace ℝ (Fin m ⊕ Fin m)) : J (frameL J e a) = frameL J e (Jv m a) := by
  simp only [frameL_apply, map_sum, map_add, map_smul, hW.JJ _ (heW _), Jv_inl, Jv_inr]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [smul_neg, neg_smul]; abel

lemma g_frame_e (a : EuclideanSpace ℝ (Fin m ⊕ Fin m)) (k : Fin m) :
    g (frameL J e a) (e k) = a (Sum.inl k) := by
  have h1 : ∀ i, g (J (e i)) (e k) = 0 := fun i => by
    rw [hW.symm _ (hW.JW _ (heW i)) _ (heW k), heJ]
  simp [frameL_apply, map_sum, hee, h1]

lemma g_frame_Je (a : EuclideanSpace ℝ (Fin m ⊕ Fin m)) (k : Fin m) :
    g (frameL J e a) (J (e k)) = a (Sum.inr k) := by
  have h1 : ∀ i, g (J (e i)) (J (e k)) = if i = k then 1 else 0 := fun i => by
    rw [hW.gJ _ (heW i) _ (heW k), hee]
  simp [frameL_apply, map_sum, heJ, h1]

lemma g_frame (a b : EuclideanSpace ℝ (Fin m ⊕ Fin m)) :
    g (frameL J e a) (frameL J e b) = inner ℝ a b := by
  conv_lhs => rw [frameL_apply e b]
  simp only [map_sum, map_add, map_smul, smul_eq_mul, g_frame_e hW heW hee heJ,
    g_frame_Je hW heW hee heJ, inner_eq_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma coord_frame (a : EuclideanSpace ℝ (Fin m ⊕ Fin m)) : coordL g J e (frameL J e a) = a := by
  ext i; cases i with
  | inl k => simp [g_frame_e hW heW hee heJ]
  | inr k => simp [g_frame_Je hW heW hee heJ]

lemma frame_coord (hspan : ∀ w ∈ W, w = ∑ k, (g w (e k) • e k + g w (J (e k)) • J (e k)))
    (w : E) (hw : w ∈ W) : frameL J e (coordL g J e w) = w := by
  rw [frameL_apply]; simp only [coordL_inl, coordL_inr]; exact (hspan w hw).symm

lemma finrank_eq (hspan : ∀ w ∈ W, w = ∑ k, (g w (e k) • e k + g w (J (e k)) • J (e k))) :
    finrank ℝ W = m + m := by
  have hinj : Function.Injective (frameL J e) := fun a b h => by
    rw [← coord_frame hW heW hee heJ a, h, coord_frame hW heW hee heJ b]
  have hr : LinearMap.range (frameL J e) = W := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩; exact frame_mem hW heW hee heJ a
    · intro w hw; exact ⟨_, frame_coord hW heW hee heJ hspan w hw⟩
  rw [← hr, LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace]
  simp

end abstract2

section vec
variable {m : ℕ}

noncomputable def ip (m : ℕ) :
    EuclideanSpace ℝ (Fin m ⊕ Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m ⊕ Fin m) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => inner ℝ a b) (fun a a' b => inner_add_left a a' b)
    (fun c a b => real_inner_smul_left a b c) (fun a b b' => inner_add_right a b b')
    (fun c a b => real_inner_smul_right a b c)

@[simp] lemma ip_apply (a b : EuclideanSpace ℝ (Fin m ⊕ Fin m)) : ip m a b = inner ℝ a b := rfl

lemma aux_mu (μ X Y : ℝ) (hX : 0 < X) (hY : 0 ≤ Y) (h : Y = -((μ ^ 2 - 4) * X)) :
    μ ^ 2 ≤ 4 ∧ -1 ≤ μ / 2 ∧ μ / 2 ≤ 1 ∧ 0 ≤ 1 - (μ / 2) ^ 2 := by
  have h4 : μ ^ 2 ≤ 4 := by nlinarith
  refine ⟨h4, by nlinarith, by nlinarith, by nlinarith⟩

set_option maxHeartbeats 1000000 in
theorem vec_oracle (M Mt : EuclideanSpace ℝ (Fin m ⊕ Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m ⊕ Fin m))
    (hM : ∀ a b, inner ℝ (M a) (M b) = inner ℝ a b) (hMJ : ∀ a, M (Jv m a) = Jv m (M a))
    (hadj : ∀ a b, inner ℝ (M a) b = inner ℝ a (Mt b)) :
    Oracle (ip m) (Jv m).toLinearMap M.toLinearMap Mt.toLinearMap ⊤ ∧
    Good (ip m) (Jv m).toLinearMap M.toLinearMap Mt.toLinearMap ⊤ := by
  have hadj' : ∀ a b, inner ℝ (Mt a) b = inner ℝ a (M b) := fun a b => by
    rw [real_inner_comm, ← hadj, real_inner_comm]
  have hMtM : ∀ a, Mt (M a) = a := fun a => ext_inner_right ℝ fun b => by
    rw [hadj', hM]
  have hMMt : ∀ a, M (Mt a) = a := by
    have h : Mt.toLinearMap * M.toLinearMap = 1 := LinearMap.ext hMtM
    have h2 := mul_eq_one_comm.1 h
    intro a; exact LinearMap.congr_fun h2 a
  have hMtJ : ∀ a, Mt (Jv m a) = Jv m (Mt a) := fun a => ext_inner_right ℝ fun b => by
    rw [hadj', inner_Jv, ← hMJ, ← hadj', inner_Jv (Mt a) b]
  refine ⟨?_, ?_⟩
  swap
  · exact { symm := fun u _ v _ => real_inner_comm v u
            pos := fun u _ hu => real_inner_self_pos.2 hu
            JW := fun _ _ => trivial
            JJ := fun u _ => Jv_Jv u
            gJ := fun u _ v _ => inner_Jv_Jv u v
            AW := fun _ _ => trivial
            BW := fun _ _ => trivial
            adj := fun u _ v _ => hadj u v
            AJ := fun u _ => hMJ u
            BJ := fun u _ => hMtJ u }
  intro W' _ hJ hA hB hne
  -- the step: normalize a nonzero complex eigenvector
  have step : ∀ w ∈ W', w ≠ 0 → ∀ θ : ℝ, M w = Real.cos θ • w + Real.sin θ • Jv m w →
      Mt w = Real.cos θ • w - Real.sin θ • Jv m w →
      ∃ e ∈ W', ip m e e = 1 ∧ ∃ θ : ℝ, M.toLinearMap e = Real.cos θ • e + Real.sin θ • (Jv m).toLinearMap e ∧
        Mt.toLinearMap e = Real.cos θ • e - Real.sin θ • (Jv m).toLinearMap e := by
    intro w hw hw0 θ h1 h2
    have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
    refine ⟨‖w‖⁻¹ • w, W'.smul_mem _ hw, ?_, θ, ?_, ?_⟩
    · rw [ip_apply, real_inner_self_eq_norm_sq, norm_smul, norm_inv, norm_norm, mul_pow, inv_pow]
      field_simp
    · simp only [ContinuousLinearMap.coe_coe, map_smul, h1]; module
    · simp only [ContinuousLinearMap.coe_coe, map_smul, h2]; module
  let S : EuclideanSpace ℝ (Fin m ⊕ Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m ⊕ Fin m) :=
    M.toLinearMap + Mt.toLinearMap
  have hS : ∀ u ∈ W', S u ∈ W' := fun u hu => W'.add_mem (hA u hu) (hB u hu)
  let S' : W' →ₗ[ℝ] W' := S.restrict hS
  have hsym : S'.IsSymmetric := by
    intro x y
    simp only [S', LinearMap.restrict_apply, Submodule.coe_inner, S, LinearMap.add_apply,
      ContinuousLinearMap.coe_coe, inner_add_left, inner_add_right]
    rw [hadj', ← hadj]
    ring
  haveI : Nontrivial W' := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, Module.End.HasEigenvalue S' μ :=
    ⟨_, hsym.hasEigenvalue_iSup_of_finiteDimensional⟩
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  set x : EuclideanSpace ℝ (Fin m ⊕ Fin m) := (v : EuclideanSpace ℝ (Fin m ⊕ Fin m)) with hxdef
  have hxW : x ∈ W' := v.2
  have hx0 : x ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hSx : M x + Mt x = μ • x := by
    have := congrArg Subtype.val hv.apply_eq_smul
    simpa [S', S] using this
  set y := M x - Mt x with hydef
  have hyW : y ∈ W' := W'.sub_mem (hA x hxW) (hB x hxW)
  have hMx : M x = (1/2 : ℝ) • (μ • x + y) := by rw [hydef, ← hSx]; module
  have hMtx : Mt x = (1/2 : ℝ) • (μ • x - y) := by rw [hydef, ← hSx]; module
  have e1 : M (M x) + Mt (Mt x) = (μ ^ 2 - 2) • x := by
    have h := congrArg (fun z => M z + Mt z) hSx
    simp only [map_add, map_smul, hMMt, hMtM] at h
    linear_combination (norm := module) h + μ • hSx
  have e2 : M (M x) - Mt (Mt x) = μ • y := by
    have h := congrArg (fun z => M z - Mt z) hSx
    simp only [map_add, map_smul, hMMt, hMtM] at h
    rw [hydef]; linear_combination (norm := module) h
  have hMy : M y = (1/2 : ℝ) • (μ • y + (μ ^ 2 - 4) • x) := by
    rw [hydef, map_sub, hMMt]; linear_combination (norm := module) (1/2 : ℝ) • e1 + (1/2 : ℝ) • e2
  have hMty : Mt y = (1/2 : ℝ) • ((4 - μ ^ 2) • x + μ • y) := by
    rw [hydef, map_sub, hMtM]; linear_combination (norm := module) (-(1/2 : ℝ)) • e1 + (1/2 : ℝ) • e2
  have hKK : M y - Mt y = (μ ^ 2 - 4) • x := by rw [hMy, hMty]; module
  have Kskew : ∀ a b, inner ℝ (M a - Mt a) b = - inner ℝ a (M b - Mt b) := fun a b => by
    rw [inner_sub_left, inner_sub_right, hadj, hadj']; ring
  have hskew : inner ℝ y y = - inner ℝ x (M y - Mt y) := by
    conv_lhs => rw [hydef]
    rw [Kskew]
  rw [hKK, inner_smul_right] at hskew
  have hxx : 0 < inner ℝ x x := real_inner_self_pos.2 hx0
  have hyy : 0 ≤ inner ℝ y y := real_inner_self_nonneg
  obtain ⟨hμ4, hμ1, hμ2, hμ5⟩ := aux_mu μ _ _ hxx hyy hskew
  have hcos : Real.cos (Real.arccos (μ / 2)) = μ / 2 := Real.cos_arccos hμ1 hμ2
  set ρ := Real.sqrt (1 - (μ / 2) ^ 2) with hρ
  have hsin : Real.sin (Real.arccos (μ / 2)) = ρ := Real.sin_arccos _
  have hρ2 : ρ ^ 2 = 1 - (μ / 2) ^ 2 := Real.sq_sqrt hμ5
  by_cases hy0 : y = 0
  · have hμ' : μ ^ 2 - 4 = 0 := by
      have := hKK; rw [hy0, map_zero, map_zero, sub_zero] at this
      exact (smul_eq_zero.1 this.symm).resolve_right hx0
    have hρ0 : ρ = 0 := by
      have : ρ ^ 2 = 0 := by rw [hρ2]; linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    refine step x hxW hx0 (Real.arccos (μ / 2)) ?_ ?_
    · rw [hcos, hsin, hρ0, hMx, hy0]; module
    · rw [hcos, hsin, hρ0, hMtx, hy0]; module
  -- general case: `w = σ x - J y` with `σ² = 4 - μ²`
  have gen : ∀ σ : ℝ, σ ^ 2 = 4 - μ ^ 2 →
      M (σ • x - Jv m y) = (μ / 2) • (σ • x - Jv m y) + (σ / 2) • Jv m (σ • x - Jv m y) ∧
      Mt (σ • x - Jv m y) = (μ / 2) • (σ • x - Jv m y) - (σ / 2) • Jv m (σ • x - Jv m y) := by
    intro σ hσ
    constructor
    · rw [map_sub, map_smul, hMJ, hMx, hMy]
      simp only [map_sub, map_smul, map_add, Jv_Jv]
      rw [show μ ^ 2 - 4 = -σ ^ 2 by linarith]
      module
    · rw [map_sub, map_smul, hMtJ, hMtx, hMty]
      simp only [map_sub, map_smul, map_add, Jv_Jv]
      rw [show 4 - μ ^ 2 = σ ^ 2 by linarith]
      module
  have hσ1 : (2 * ρ) ^ 2 = 4 - μ ^ 2 := by rw [mul_pow, hρ2]; ring
  have hσ2 : (-(2 * ρ)) ^ 2 = 4 - μ ^ 2 := by rw [neg_sq, hσ1]
  have hwW : ∀ σ : ℝ, σ • x - Jv m y ∈ W' := fun σ => W'.sub_mem (W'.smul_mem _ hxW) (hJ y hyW)
  by_cases hw1 : (2 * ρ) • x - Jv m y = 0
  · have hw2 : (-(2 * ρ)) • x - Jv m y ≠ 0 := by
      intro hw2
      have h4 : (4 * ρ) • x = 0 := by
        have := congrArg₂ (· - ·) hw1 hw2; simp only [sub_zero] at this
        rw [← this]; module
      have hρ0 : ρ = 0 := by
        have := (smul_eq_zero.1 h4).resolve_right hx0; linarith
      apply hy0
      have : inner ℝ y y = 0 := by
        rw [hskew]; have : μ ^ 2 - 4 = 0 := by rw [hρ0] at hρ2; linarith
        rw [this]; simp
      exact inner_self_eq_zero.1 this
    obtain ⟨h1, h2⟩ := gen _ hσ2
    refine step _ (hwW _) hw2 (-Real.arccos (μ / 2)) ?_ ?_
    · rw [Real.cos_neg, Real.sin_neg, hcos, hsin, h1]; module
    · rw [Real.cos_neg, Real.sin_neg, hcos, hsin, h2]; module
  · obtain ⟨h1, h2⟩ := gen _ hσ1
    refine step _ (hwW _) hw1 (Real.arccos (μ / 2)) ?_ ?_
    · rw [hcos, hsin, h1]; module
    · rw [hcos, hsin, h2]; module

/-- Unitary normal form of an orthogonal `J₀`-linear map of `ℝ^{2m}`. -/
theorem vec_nf (M : EuclideanSpace ℝ (Fin m ⊕ Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m ⊕ Fin m))
    (hM : ∀ a b, inner ℝ (M a) (M b) = inner ℝ a b) (hMJ : ∀ a, M (Jv m a) = Jv m (M a)) :
    ∃ f : Fin m → EuclideanSpace ℝ (Fin m ⊕ Fin m), ∃ θ : Fin m → ℝ,
      (∀ i j, inner ℝ (f i) (f j) = if i = j then 1 else 0) ∧ (∀ i j, inner ℝ (f i) (Jv m (f j)) = 0) ∧
      (∀ k, M (f k) = Real.cos (θ k) • f k + Real.sin (θ k) • Jv m (f k)) ∧
      (∀ w, w = ∑ k, (inner ℝ w (f k) • f k + inner ℝ w (Jv m (f k)) • Jv m (f k))) := by
  obtain ⟨hO, hG⟩ := vec_oracle M (ContinuousLinearMap.adjoint M) hM hMJ
    (fun a b => (ContinuousLinearMap.adjoint_inner_right M a b).symm)
  obtain ⟨m', f, θ, hfW, hff, hfJ, hMf, hspan⟩ := nf ⊤ hG hO
  have hrk := finrank_eq hG hfW hff hfJ hspan
  rw [finrank_top, finrank_euclideanSpace] at hrk
  simp only [Fintype.card_sum, Fintype.card_fin] at hrk
  obtain rfl : m' = m := by omega
  exact ⟨f, θ, hff, hfJ, hMf, fun w => hspan w trivial⟩

end vec

end UFrame



set_option linter.all false

open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff

namespace IsoSpec
open FiniteEnergyPlane
open scoped ContDiff

variable {n : ℕ}

lemma contDiff_j0 : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 fun k => ?_
  unfold j0
  by_cases h : (k : ℕ) % 2 = 0
  · simp only [h, dite_true]
    exact (contDiff_apply ℝ ℝ _).neg
  · simp only [h, dite_false]
    exact contDiff_apply ℝ ℝ _

lemma contDiff_hamVF (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (hamVF H) := by
  have hg : ContDiff ℝ ∞ (grad H) := by
    refine contDiff_pi.2 fun k => ?_
    exact (hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact contDiff_j0.comp hg

lemma contDiff_liouville : ContDiff ℝ ∞ (fun p : V n × V n => liouville p.1 p.2) := by
  unfold liouville omega0 dot
  refine ContDiff.div_const (ContDiff.sum fun k _ => ?_) _
  exact ((contDiff_apply ℝ ℝ k).comp (contDiff_j0.comp contDiff_fst)).mul
    ((contDiff_apply ℝ ℝ k).comp contDiff_snd)

lemma liouvilleCLM_apply (x v : V n) : liouvilleCLM x v = liouville x v := by
  simp [liouvilleCLM, liouville, omega0, dot, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end IsoSpec

namespace FrameBridge

variable {n : ℕ}

lemma j0_add (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; by_cases h : (k : ℕ) % 2 = 0 <;> simp [j0, h]; ring

lemma j0_smul (c : ℝ) (u : V n) : j0 (c • u) = c • j0 u := by
  funext k; by_cases h : (k : ℕ) % 2 = 0 <;> simp [j0, h]

lemma om_add_left (u u' v : V n) : omega0 (u + u') v = omega0 u v + omega0 u' v := by
  simp [omega0, dot, j0_add, add_mul, Finset.sum_add_distrib]

lemma om_smul_left (c : ℝ) (u v : V n) : omega0 (c • u) v = c * omega0 u v := by
  simp [omega0, dot, j0_smul, Finset.mul_sum, mul_assoc]

lemma om_add_right (u v v' : V n) : omega0 u (v + v') = omega0 u v + omega0 u v' := by
  simp [omega0, dot, mul_add, Finset.sum_add_distrib]

lemma om_smul_right (c : ℝ) (u v : V n) : omega0 u (c • v) = c * omega0 u v := by
  simp [omega0, dot, Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def om : V n →L[ℝ] V n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V n →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V n →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ omega0 om_add_left om_smul_left om_add_right om_smul_right)

@[simp] lemma om_apply (u v : V n) : om u v = omega0 u v := rfl

/-- the coordinate involution `k ↦ k xor 1` -/
def sw (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

lemma sw_sw (k : Fin (2 * (n + 1))) : sw (sw k) = k := by
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [sw, h, h', ↓reduceDIte, Fin.ext_iff]; omega
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [sw, h, h', ↓reduceDIte, Fin.ext_iff]; omega

lemma om_antisymm (u v : V n) : omega0 u v = -omega0 v u := by
  have e : Function.Involutive (sw (n := n)) := sw_sw
  simp only [omega0, dot]
  rw [← Equiv.sum_comp e.toPerm (fun k => j0 u k * v k)]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.Involutive.coe_toPerm, j0, sw]
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [h, h', ↓reduceDIte]
    have : (⟨(k : ℕ) + 1 - 1, by omega⟩ : Fin (2 * (n + 1))) = k := by ext; simp
    rw [this]; ring
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [h, h', ↓reduceDIte]
    have : (⟨(k : ℕ) - 1 + 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
      ext; simp; omega
    rw [this]; ring


open CauchyRiemannIndex

/-- `J₀` acting on `ℝ^{2n}`. -/
noncomputable abbrev JL (n : ℕ) : Vec n →L[ℝ] Vec n :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (J₀ n))

noncomputable abbrev e (i : Fin n ⊕ Fin n) : Vec n := EuclideanSpace.single i (1 : ℝ)

lemma JL_apply (c : Vec n) : JL n c = Matrix.toEuclideanLin (J₀ n) c := rfl

lemma JJ (c : Vec n) : Matrix.toEuclideanLin (J₀ n) (Matrix.toEuclideanLin (J₀ n) c) = -c := by
  simp only [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.J_squared]
  ext i; simp [Matrix.neg_mulVec]

lemma vec_expand (c : Vec n) : c = ∑ j, c j • e j := by
  have := (EuclideanSpace.basisFun (Fin n ⊕ Fin n) ℝ).sum_repr c
  simpa [e] using this.symm

lemma om_zero_left (v : V n) : omega0 0 v = 0 := by rw [← om_apply]; simp
lemma om_zero_right (v : V n) : omega0 v 0 = 0 := by rw [← om_apply, map_zero]
lemma om_sub_left (u u' v : V n) : omega0 (u - u') v = omega0 u v - omega0 u' v := by
  simp only [← om_apply, map_sub, ContinuousLinearMap.sub_apply]
lemma om_neg_left (u v : V n) : omega0 (-u) v = -omega0 u v := by
  simp only [← om_apply, map_neg, ContinuousLinearMap.neg_apply]
lemma om_sum_left {ι : Type*} (s : Finset ι) (f : ι → V n) (v : V n) :
    omega0 (∑ i ∈ s, f i) v = ∑ i ∈ s, omega0 (f i) v := by
  simp only [← om_apply, map_sum, ContinuousLinearMap.sum_apply]

/-! ### `ξ` is a linear subspace -/

lemma liou_lin (x : V n) : (fun v => liouville x v) = fun v => om x v / 2 := rfl

lemma xi_add {H : V n → ℝ} {y u v : V n} (hu : IsInXi H y u) (hv : IsInXi H y v) :
    IsInXi H y (u + v) := by
  refine ⟨?_, ?_⟩
  · have h1 := hu.1; have h2 := hv.1
    simp only [liouville, ← om_apply] at h1 h2 ⊢; rw [map_add]; linarith
  · rw [map_add, hu.2, hv.2, add_zero]

lemma xi_smul {H : V n → ℝ} {y u : V n} (c : ℝ) (hu : IsInXi H y u) : IsInXi H y (c • u) := by
  refine ⟨?_, ?_⟩
  · have h1 := hu.1
    simp only [liouville, ← om_apply] at h1 ⊢; rw [map_smul, smul_eq_mul]
    have : om y u = 0 := by linarith
    rw [this]; simp
  · rw [map_smul, hu.2, smul_zero]

lemma xi_neg {H : V n → ℝ} {y u : V n} (hu : IsInXi H y u) : IsInXi H y (-u) := by
  simpa using xi_smul (-1) hu

lemma xi_sub {H : V n → ℝ} {y u v : V n} (hu : IsInXi H y u) (hv : IsInXi H y v) :
    IsInXi H y (u - v) := by
  simpa [sub_eq_add_neg] using xi_add hu (xi_neg hv)

/-! ### Unitary frames -/

/-! ### Analytic facts along the orbit -/

def shiftOrbit {H : V n → ℝ} (P : ReebOrbit H) (τ : ℝ) : ReebOrbit H where
  x := fun s => P.x (s + τ)
  T := P.T
  T_pos := P.T_pos
  mem := fun s => P.mem _
  hasDerivAt := fun s => (P.hasDerivAt (s + τ)).comp_add_const s τ
  periodic := fun s => by
    show P.x (s + P.T + τ) = P.x (s + τ)
    rw [show s + P.T + τ = (s + τ) + P.T by ring]; exact P.periodic _

lemma om_cont : Continuous fun p : V n × V n => omega0 p.1 p.2 := by
  have : (fun p : V n × V n => omega0 p.1 p.2) = fun p => om p.1 p.2 := rfl
  rw [this]; exact (om.continuous.comp continuous_fst).clm_apply continuous_snd

lemma xi_limit {H : V n → ℝ} (hH : ContDiff ℝ 1 H) {l : Filter ℝ} [l.NeBot] {f g : ℝ → V n}
    {y v : V n} (hf : Tendsto f l (𝓝 y)) (hg : Tendsto g l (𝓝 v))
    (hev : ∀ᶠ s in l, IsInXi H (f s) (g s)) : IsInXi H y v := by
  constructor
  · have h1 : Tendsto (fun s => liouville (f s) (g s)) l (𝓝 (liouville y v)) := by
      have := (om_cont (n := n)).continuousAt (x := (y, v))
      have h := (this.tendsto.comp (hf.prodMk_nhds hg)).div_const 2
      simpa [liouville] using h
    exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (hev.mono fun s hs => hs.1.symm))
  · have hc : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by simp)
    have h1 : Tendsto (fun s => fderiv ℝ H (f s) (g s)) l (𝓝 (fderiv ℝ H y v)) := by
      have := ((hc.comp continuous_fst).clm_apply (continuous_snd (X := V n) (Y := V n))).continuousAt
        (x := (y, v))
      exact this.tendsto.comp (hf.prodMk_nhds hg)
    exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (hev.mono fun s hs => hs.2.symm))

/-- derivative of `ω₀(f, g)` -/
lemma hasDerivAt_om {f g : ℝ → V n} {f' g' : V n} {t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => omega0 (f s) (g s)) (omega0 f' (g t) + omega0 (f t) g') t := by
  have h1 : HasDerivAt (fun s => om (f s)) (om f') t := om.hasFDerivAt.comp_hasDerivAt t hf
  exact h1.clm_apply hg

section lode_sec
section lode
open Set Filter Topology
open scoped NNReal
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma uf_lode_local (B : ℝ → F →L[ℝ] F) (hB : Continuous B) (K : ℝ≥0)
    (hK : ∀ t, ‖B t‖₊ ≤ K) (h : ℝ) (hh : 0 < h) (hKh : 2 * (K:ℝ) * h ≤ 1) (s : ℝ) (x₀ : F) :
    ∃ y : ℝ → F, y s = x₀ ∧ ∀ t ∈ Icc (s - h) (s + h),
      HasDerivWithinAt y (B t (y t)) (Icc (s - h) (s + h)) t := by
  have hs : s ∈ Icc (s - h) (s + h) := ⟨by linarith, by linarith⟩
  have hP : IsPicardLindelof (fun t => (B t : F → F)) (⟨s, hs⟩ : Icc (s-h) (s+h)) x₀
      (‖x₀‖₊ + 1) 0 (K * (2 * ‖x₀‖₊ + 1)) K := by
    refine ⟨fun t _ => ((B t).lipschitz.weaken (hK t)).lipschitzOnWith,
      fun x _ => (hB.clm_apply continuous_const).continuousOn, fun t _ x hx => ?_, ?_⟩
    · have hx' : ‖x‖ ≤ 2 * ‖x₀‖ + 1 := by
        have h1 := mem_closedBall_iff_norm.1 hx
        have h2 := norm_le_norm_add_norm_sub' x x₀
        push_cast at h1; linarith
      have hKt : ‖B t‖ ≤ K := by exact_mod_cast hK t
      calc ‖B t x‖ ≤ ‖B t‖ * ‖x‖ := (B t).le_opNorm x
        _ ≤ K * (2 * ‖x₀‖ + 1) := mul_le_mul hKt hx' (norm_nonneg _) K.2
        _ = ((K * (2 * ‖x₀‖₊ + 1) : ℝ≥0) : ℝ) := by push_cast; rfl
    · have e1 : (s + h) - s = h := by ring
      have e2 : s - (s - h) = h := by ring
      simp only [e1, e2, max_self, NNReal.coe_zero, sub_zero]
      push_cast
      have := norm_nonneg x₀
      have hK0 := K.2
      nlinarith
  obtain ⟨y, hy0, hy⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨y, hy0, hy⟩

lemma uf_piece {y g : ℝ → F} {S : Set ℝ} (hS : IsClosed S) (B : ℝ → F →L[ℝ] F)
    (heq : EqOn y g S) (hg : ∀ t ∈ S, HasDerivWithinAt g (B t (g t)) S t) (t : ℝ) :
    HasDerivWithinAt y (B t (y t)) S t := by
  by_cases ht : t ∈ S
  · rw [heq ht]; exact (hg t ht).congr (fun x hx => heq hx) (heq ht)
  · exact hasDerivWithinAt_iff_hasFDerivWithinAt.2
      (HasFDerivWithinAt.of_notMem_closure (by rwa [hS.closure_eq]))

lemma uf_lode_steps (B : ℝ → F →L[ℝ] F) (hB : Continuous B) (K : ℝ≥0)
    (hK : ∀ t, ‖B t‖₊ ≤ K) (h : ℝ) (hh : 0 < h) (hKh : 2 * (K:ℝ) * h ≤ 1) (x₀ : F) (N : ℕ) :
    ∃ y : ℝ → F, y 0 = x₀ ∧ ∀ t ∈ Icc (-((N+1) * h)) ((N+1) * h),
      HasDerivWithinAt y (B t (y t)) (Icc (-((N+1) * h)) ((N+1) * h)) t := by
  induction N with
  | zero =>
    obtain ⟨y, hy0, hy⟩ := uf_lode_local B hB K hK h hh hKh 0 x₀
    refine ⟨y, hy0, ?_⟩
    simpa using hy
  | succ N ih =>
    obtain ⟨y, hy0, hy⟩ := ih
    set c : ℝ := (N + 1) * h with hc
    have hc0 : 0 < c := by positivity
    obtain ⟨u, hu0, hu⟩ := uf_lode_local B hB K hK h hh hKh c (y c)
    obtain ⟨w, hw0, hw⟩ := uf_lode_local B hB K hK h hh hKh (-c) (y (-c))
    let z : ℝ → F := fun t => if c < t then u t else if t < -c then w t else y t
    have hcc : ((N + 1 : ℕ) + 1 : ℝ) * h = c + h := by push_cast; rw [hc]; ring
    refine ⟨z, ?_, ?_⟩
    · simp only [z, if_neg (show ¬ c < 0 by linarith), if_neg (show ¬ (0:ℝ) < -c by linarith), hy0]
    rw [hcc]
    have hU : Icc (-(c + h)) (c + h) = (Icc (-(c+h)) (-c) ∪ Icc (-c) c) ∪ Icc c (c + h) := by
      rw [Icc_union_Icc_eq_Icc (by linarith) (by linarith),
        Icc_union_Icc_eq_Icc (by linarith) (by linarith)]
    intro t _
    rw [hU]
    refine HasDerivWithinAt.union (HasDerivWithinAt.union ?_ ?_) ?_
    · refine uf_piece isClosed_Icc B (g := w) ?_ ?_ t
      · intro s hs
        simp only [z]
        rcases eq_or_lt_of_le hs.2 with h1 | h1
        · rw [if_neg (by linarith), if_neg (by linarith), h1, hw0]
        · rw [if_neg (by linarith), if_pos h1]
      · intro s hs
        exact (hw s ⟨by linarith [hs.1], by linarith [hs.2]⟩).mono
          (Icc_subset_Icc (by linarith) (by linarith))
    · refine uf_piece isClosed_Icc B (g := y) ?_ ?_ t
      · intro s hs
        simp only [z]; rw [if_neg (by linarith [hs.2]), if_neg (by linarith [hs.1])]
      · intro s hs; exact hy s hs
    · refine uf_piece isClosed_Icc B (g := u) ?_ ?_ t
      · intro s hs
        simp only [z]
        rcases eq_or_lt_of_le hs.1 with h1 | h1
        · rw [if_neg (by linarith), if_neg (by linarith), ← h1, hu0]
        · rw [if_pos h1]
      · intro s hs
        exact (hu s ⟨by linarith [hs.1], by linarith [hs.2]⟩).mono
          (Icc_subset_Icc (by linarith) (by linarith))

lemma uf_lode_exists (B : ℝ → F →L[ℝ] F) (hB : Continuous B) (K : ℝ≥0)
    (hK : ∀ t, ‖B t‖₊ ≤ K) (x₀ : F) :
    ∃ y : ℝ → F, y 0 = x₀ ∧ ∀ t, HasDerivAt y (B t (y t)) t := by
  set h : ℝ := 1 / (2 * (K:ℝ) + 1) with hhdef
  have hh : 0 < h := by positivity
  have hKh : 2 * (K:ℝ) * h ≤ 1 := by
    rw [hhdef, mul_one_div, div_le_one (by positivity)]; linarith
  choose Ψ hΨ0 hΨ using uf_lode_steps B hB K hK h hh hKh x₀
  have hint : ∀ M : ℕ, ∀ t ∈ Ioo (-((M+1) * h)) ((M+1) * h), HasDerivAt (Ψ M) (B t (Ψ M t)) t := by
    intro M t ht
    exact (hΨ M t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hagree : ∀ M N : ℕ, ∀ s, |s| < (min M N + 1) * h → Ψ M s = Ψ N s := by
    intro M N s hs
    have hk : ((min M N : ℕ) : ℝ) = min (M:ℝ) (N:ℝ) := by push_cast; rfl
    have hsub : ∀ L : ℕ, min M N ≤ L → Ioo (-((min M N + 1) * h)) ((min M N + 1) * h) ⊆
        Ioo (-((L+1) * h)) ((L+1) * h) := by
      intro L hL
      have : ((min M N : ℕ) : ℝ) ≤ L := by exact_mod_cast hL
      apply Ioo_subset_Ioo <;> nlinarith
    have := ODE_solution_unique_of_mem_Ioo (K := K) (v := fun t => (B t : F → F))
      (s := fun _ => (univ : Set F)) (f := Ψ M) (g := Ψ N)
      (a := -((min M N + 1) * h)) (b := (min M N + 1) * h) (t₀ := 0)
      (fun t _ => ((B t).lipschitz.weaken (hK t)).lipschitzOnWith)
      ⟨by have : (0:ℝ) ≤ min M N := by positivity
          nlinarith, by positivity⟩
      (fun t ht => ⟨hint M t (hsub M (min_le_left _ _) ht), trivial⟩)
      (fun t ht => ⟨hint N t (hsub N (min_le_right _ _) ht), trivial⟩)
      (by rw [hΨ0, hΨ0])
    exact this ⟨by rw [abs_lt] at hs; push_cast at hs ⊢; linarith, by rw [abs_lt] at hs; push_cast at hs ⊢; linarith⟩
  let Nf : ℝ → ℕ := fun t => ⌈|t| / h⌉₊
  have hNf : ∀ t, |t| ≤ Nf t * h := by
    intro t
    have := Nat.le_ceil (|t| / h)
    rwa [div_le_iff₀ hh] at this
  refine ⟨fun t => Ψ (Nf t) t, ?_, ?_⟩
  · exact hΨ0 _
  intro t
  set M := Nf t
  have hev : (fun s => Ψ (Nf s) s) =ᶠ[𝓝 t] Ψ M := by
    have hmem : Ioo (-((M+1) * h)) ((M+1) * h) ∈ 𝓝 t := by
      apply Ioo_mem_nhds
      · have := hNf t; have := neg_abs_le t; nlinarith
      · have := hNf t; have := le_abs_self t; nlinarith
    filter_upwards [hmem] with s hs
    apply hagree
    have h1 := hNf s
    have hs' : |s| < (M + 1) * h := abs_lt.2 ⟨by linarith [hs.1], hs.2⟩
    rcases le_total (Nf s) M with hle | hle
    · rw [min_eq_left hle]; nlinarith
    · rw [min_eq_right hle]; exact hs'
  have hd := hint M t ⟨by have := hNf t; have := neg_abs_le t; nlinarith,
    by have := hNf t; have := le_abs_self t; nlinarith⟩
  have := hd.congr_of_eventuallyEq hev
  exact this

lemma uf_lode_unique (B : ℝ → F →L[ℝ] F) (K : ℝ≥0) (hK : ∀ t, ‖B t‖₊ ≤ K)
    (y z : ℝ → F) (hy : ∀ t, HasDerivAt y (B t (y t)) t) (hz : ∀ t, HasDerivAt z (B t (z t)) t)
    (t₀ : ℝ) (h0 : y t₀ = z t₀) : y = z :=
  ODE_solution_unique_univ (K := K) (v := fun t => (B t : F → F)) (s := fun _ => (univ : Set F))
    (fun t => ((B t).lipschitz.weaken (hK t)).lipschitzOnWith)
    (fun t => ⟨hy t, trivial⟩) (fun t => ⟨hz t, trivial⟩) h0

end lode

variable {n : ℕ}
end lode_sec

section orbit
variable {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
include hH

lemma reeb_smooth : ∃ U : Set (V n), IsOpen U ∧ ContDiffOn ℝ ∞ (reeb H) U ∧ ∀ τ, P.x τ ∈ U := by
  set D : V n → ℝ := fun y => liouville y (hamVF H y) with hDdef
  have hD : ContDiff ℝ ∞ D := by
    have h1 := IsoSpec.contDiff_liouville (n := n)
    have h2 := IsoSpec.contDiff_hamVF H hH.1
    exact h1.comp (contDiff_id.prodMk h2)
  refine ⟨{y | 0 < D y}, isOpen_lt continuous_const hD.continuous, ?_, fun τ =>
    (reeb_spec H hH (P.x τ) (P.mem τ)).1⟩
  have : reeb H = fun y => (D y)⁻¹ • hamVF H y := rfl
  rw [this]
  have h1 : ContDiffOn ℝ ∞ (fun y => (D y)⁻¹) {y | 0 < D y} :=
    hD.contDiffOn.inv fun y hy => ne_of_gt hy
  exact h1.smul (IsoSpec.contDiff_hamVF H hH.1).contDiffOn

lemma x_smooth : ContDiff ℝ ∞ P.x := by
  obtain ⟨U, hU, hR, hxU⟩ := reeb_smooth hH P
  have hdx : deriv P.x = fun τ => reeb H (P.x τ) := funext fun τ => (P.hasDerivAt τ).deriv
  have hdiff : Differentiable ℝ P.x := fun τ => (P.hasDerivAt τ).differentiableAt
  have key : ∀ m : ℕ, ContDiff ℝ m P.x := by
    intro m
    induction m with
    | zero => exact contDiff_zero.2 hdiff.continuous
    | succ m ih =>
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl]
      refine contDiff_succ_iff_deriv.2 ⟨hdiff, by simp, ?_⟩
      rw [hdx]
      exact (hR.of_le (by exact_mod_cast le_top)).comp_contDiff ih hxU
  exact contDiff_infty.2 key

end orbit


/-! ## The transported structures -/

section ops
variable {H : V n → ℝ}

/-- the loop `t ↦ x(Tt)` -/
def gam (P : ReebOrbit H) (t : ℝ) : V n := P.x (P.T * t)

lemma gam_mem (P : ReebOrbit H) (t : ℝ) : gam P t ∈ energySurface H := P.mem _

lemma gam_periodic (P : ReebOrbit H) (t : ℝ) : gam P (t + 1) = gam P t := by
  simp only [gam]; rw [show P.T * (t + 1) = P.T * t + P.T by ring, P.periodic]

/-- the `ω₀`-orthogonal projection onto `ξ` along `span {x, R}` -/
noncomputable def Pr (P : ReebOrbit H) (t : ℝ) : V n →L[ℝ] V n :=
  ContinuousLinearMap.id ℝ (V n)
    - (fderiv ℝ H (gam P t) (gam P t))⁻¹ • (fderiv ℝ H (gam P t)).smulRight (gam P t)
    - (liouvilleCLM (gam P t)).smulRight (reeb H (gam P t))

lemma Pr_apply (P : ReebOrbit H) (t : ℝ) (v : V n) :
    Pr P t v = v - (fderiv ℝ H (gam P t) v / fderiv ℝ H (gam P t) (gam P t)) • gam P t
      - liouville (gam P t) v • reeb H (gam P t) := by
  simp [Pr, IsoSpec.liouvilleCLM_apply, smul_smul, div_eq_inv_mul]

lemma Pr_periodic (P : ReebOrbit H) (t : ℝ) : Pr P (t + 1) = Pr P t := by
  simp only [Pr, gam_periodic]

variable (J : V n → V n →L[ℝ] V n)

noncomputable def Iop (P : ReebOrbit H) (t : ℝ) : V n →L[ℝ] V n := (J (gam P t)).comp (Pr P t)

lemma Iop_periodic (P : ReebOrbit H) (t : ℝ) : Iop J P (t + 1) = Iop J P t := by
  simp only [Iop, Pr_periodic, gam_periodic]

variable {J} (hH : IsStrictlyStarShapedLevel H) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)

lemma om_neg_right (u v : V n) : omega0 u (-v) = -omega0 u v := by
  simp only [← om_apply, map_neg]

lemma liou_self (x : V n) : liouville x x = 0 := by
  have := om_antisymm x x; simp only [liouville]; linarith

lemma liou_lin' (x u v : V n) (a b : ℝ) :
    liouville x (a • u + b • v) = a * liouville x u + b * liouville x v := by
  simp only [← IsoSpec.liouvilleCLM_apply, map_add, map_smul, smul_eq_mul]

include hH in
lemma Pr_xi (t : ℝ) (v : V n) : IsInXi H (gam P t) (Pr P t v) := by
  obtain ⟨h1, h2, h3, -⟩ := reeb_spec H hH (gam P t) (gam_mem P t)
  have hpos : 0 < fderiv ℝ H (gam P t) (gam P t) := hH.2.2 _ (gam_mem P t)
  rw [Pr_apply]
  constructor
  · simp only [← IsoSpec.liouvilleCLM_apply, map_sub, map_smul, smul_eq_mul] at h2 ⊢
    rw [IsoSpec.liouvilleCLM_apply (gam P t) (gam P t), liou_self, h2]; ring
  · simp only [map_sub, map_smul, smul_eq_mul, h3]; field_simp; ring

lemma Pr_of_xi (t : ℝ) (v : V n) (hv : IsInXi H (gam P t) v) : Pr P t v = v := by
  rw [Pr_apply, hv.1, hv.2]; simp

include hH in
lemma Pr_idem (t : ℝ) (v : V n) : Pr P t (Pr P t v) = Pr P t v := Pr_of_xi P t _ (Pr_xi hH P t v)

include hH in
/-- `v - P v ∈ span {x, R}` is `ω₀`-orthogonal to `ξ` -/
lemma kerP_orth (t : ℝ) (v b : V n) (hb : IsInXi H (gam P t) b) :
    omega0 (v - Pr P t v) b = 0 := by
  obtain ⟨-, -, -, h4⟩ := reeb_spec H hH (gam P t) (gam_mem P t)
  have e : v - Pr P t v = (fderiv ℝ H (gam P t) v / fderiv ℝ H (gam P t) (gam P t)) • gam P t
      + liouville (gam P t) v • reeb H (gam P t) := by rw [Pr_apply]; abel
  rw [e, om_add_left, om_smul_left, om_smul_left, h4 b hb.2]
  have : omega0 (gam P t) b = 0 := by have := hb.1; simp only [liouville] at this; linarith
  rw [this]; ring

include hH in
lemma kerP_orth' (t : ℝ) (v b : V n) (hb : IsInXi H (gam P t) b) :
    omega0 b (v - Pr P t v) = 0 := by
  rw [om_antisymm, kerP_orth hH P t v b hb, neg_zero]

include hH hJ in
lemma Iop_xi (t : ℝ) (v : V n) : IsInXi H (gam P t) (Iop J P t v) :=
  (hJ.2 _ (gam_mem P t) _ _ (Pr_xi hH P t v) (Pr_xi hH P t v)).1

include hH hJ in
lemma Iop_Iop (t : ℝ) (v : V n) : Iop J P t (Iop J P t v) = - Pr P t v := by
  simp only [Iop, ContinuousLinearMap.comp_apply]
  have hx := Pr_xi hH P t v
  rw [Pr_of_xi P t _ (hJ.2 _ (gam_mem P t) _ _ hx hx).1, (hJ.2 _ (gam_mem P t) _ _ hx hx).2.1]

include hH in
lemma Iop_Pr (t : ℝ) (v : V n) : Iop J P t (Pr P t v) = Iop J P t v := by
  simp only [Iop, ContinuousLinearMap.comp_apply, Pr_idem hH P t v]

include hH hJ in
lemma Pr_Iop (t : ℝ) (v : V n) : Pr P t (Iop J P t v) = Iop J P t v :=
  Pr_of_xi P t _ (Iop_xi hH hJ P t v)

include hH hJ in
lemma Iop_skew (t : ℝ) (u w : V n) : omega0 (Iop J P t u) w = - omega0 u (Iop J P t w) := by
  have hu := Pr_xi hH P t u
  have hw := Pr_xi hH P t w
  have hIu := Iop_xi hH hJ P t u
  have hIw := Iop_xi hH hJ P t w
  have e1 : omega0 (Iop J P t u) w = omega0 (Iop J P t u) (Pr P t w) := by
    have := kerP_orth' hH P t w _ hIu
    rw [om_antisymm, om_sub_left] at this
    rw [om_antisymm (Iop J P t u) w, om_antisymm (Iop J P t u) (Pr P t w)]; linarith
  have e2 : omega0 (Iop J P t u) (Pr P t w) = - omega0 (Pr P t u) (Iop J P t w) := by
    have hc := (hJ.2 _ (gam_mem P t) _ _ hu hIw).2.2.2
    simp only [Iop, ContinuousLinearMap.comp_apply] at hc ⊢
    rw [(hJ.2 _ (gam_mem P t) _ _ hw hw).2.1, om_neg_right] at hc
    linarith
  have e3 : omega0 (Pr P t u) (Iop J P t w) = omega0 u (Iop J P t w) := by
    have := kerP_orth hH P t u _ hIw
    rw [om_sub_left] at this; linarith
  rw [e1, e2, e3]

/-! ### ring identities -/

include hH in
lemma PP (t : ℝ) : Pr P t * Pr P t = Pr P t := ContinuousLinearMap.ext fun v => Pr_idem hH P t v
include hH in
lemma IP (t : ℝ) : Iop J P t * Pr P t = Iop J P t := ContinuousLinearMap.ext fun v => Iop_Pr hH P t v
include hH hJ in
lemma PI (t : ℝ) : Pr P t * Iop J P t = Iop J P t := ContinuousLinearMap.ext fun v => Pr_Iop hH hJ P t v
include hH hJ in
lemma II (t : ℝ) : Iop J P t * Iop J P t = - Pr P t := ContinuousLinearMap.ext fun v => Iop_Iop hH hJ P t v

/-! ### smoothness -/

include hH in
lemma gam_smooth : ContDiff ℝ ∞ (gam P) :=
  (x_smooth hH P).comp (contDiff_const.mul contDiff_id)

include hH in
lemma Pr_smooth : ContDiff ℝ ∞ (Pr P) := by
  have hg := gam_smooth hH P
  have hdH : ContDiff ℝ ∞ (fun t => fderiv ℝ H (gam P t)) :=
    (hH.1.fderiv_right (m := ∞) (by simp)).comp hg
  have hh : ContDiff ℝ ∞ (fun t => fderiv ℝ H (gam P t) (gam P t)) := hdH.clm_apply hg
  have hinv : ContDiff ℝ ∞ (fun t => (fderiv ℝ H (gam P t) (gam P t))⁻¹) :=
    hh.inv fun t => (hH.2.2 _ (gam_mem P t)).ne'
  have eSR : ∀ (c : V n →L[ℝ] ℝ) (f : V n),
      ContinuousLinearMap.smulRightL ℝ (V n) (V n) c f = c.smulRight f := fun c f => by
    ext; simp
  have hsr1 : ContDiff ℝ ∞ (fun t => (fderiv ℝ H (gam P t)).smulRight (gam P t)) := by
    have := ((ContinuousLinearMap.smulRightL ℝ (V n) (V n)).contDiff.comp hdH).clm_apply hg
    simpa only [Function.comp_def, eSR] using this
  have hL : ContDiff ℝ ∞ (fun t => liouvilleCLM (gam P t)) := by
    unfold liouvilleCLM
    refine ContDiff.const_smul _ (ContDiff.sum fun k _ => ?_)
    exact ((contDiff_apply ℝ ℝ k).comp (IsoSpec.contDiff_j0.comp hg)).smul contDiff_const
  obtain ⟨U, hU, hR, hxU⟩ := reeb_smooth hH P
  have hRg : ContDiff ℝ ∞ (fun t => reeb H (gam P t)) := hR.comp_contDiff hg fun t => hxU _
  have hsr2 : ContDiff ℝ ∞ (fun t => (liouvilleCLM (gam P t)).smulRight (reeb H (gam P t))) := by
    have := ((ContinuousLinearMap.smulRightL ℝ (V n) (V n)).contDiff.comp hL).clm_apply hRg
    simpa only [Function.comp_def, eSR] using this
  exact (contDiff_const.sub (hinv.smul hsr1)).sub hsr2

include hH hJ in
lemma Iop_smooth : ContDiff ℝ ∞ (Iop J P) :=
  (hJ.1.comp (gam_smooth hH P)).clm_comp (Pr_smooth hH P)

end ops

/-! ## The Kato transport -/

lemma lax_alg {R : Type*} [Ring R] [Algebra ℝ R] (p i p' i' : R) (h1 : p * p = p) (h2 : i * p = i)
    (h3 : p * i = i) (h4 : i * i = -p) (d1 : p' * p + p * p' = p') (d2 : i' * p + i * p' = i')
    (d3 : p' * i + p * i' = i') (d4 : i' * i + i * i' = -p') :
    ((3/2 : ℝ) • (p' * p) - p' - (1/2 : ℝ) • (i' * i)) * p
        - p * ((3/2 : ℝ) • (p' * p) - p' - (1/2 : ℝ) • (i' * i)) = p' ∧
    ((3/2 : ℝ) • (p' * p) - p' - (1/2 : ℝ) • (i' * i)) * i
        - i * ((3/2 : ℝ) • (p' * p) - p' - (1/2 : ℝ) • (i' * i)) = i' := by
  have e1 : p * (p' * p) = 0 := by
    have := congrArg (· * p) d1
    simp only [add_mul, mul_assoc, h1] at this
    simpa using this
  have e2 : p * i' = i' - p' * i := eq_sub_of_add_eq' d3
  have e3 : i * p' = i' - i' * p := eq_sub_of_add_eq' d2
  have e4 : i * i' = -p' - i' * i := eq_sub_of_add_eq' d4
  have e5 : i * (p' * p) = 0 := by rw [← mul_assoc, e3, sub_mul, mul_assoc, h1, sub_self]
  constructor
  · have hc : ((3/2 : ℝ) • (p' * p) - p' - (1/2 : ℝ) • (i' * i)) * p
        = (3/2 : ℝ) • (p' * p) - p' * p - (1/2 : ℝ) • (i' * i) := by
      simp only [sub_mul, smul_mul_assoc, mul_assoc, h1, h2]
    have hc' : p * ((3/2 : ℝ) • (p' * p) - p' - (1/2 : ℝ) • (i' * i))
        = - (p * p') - (1/2 : ℝ) • (i' * i + p' * p) := by
      simp only [mul_sub, mul_smul_comm, e1]
      rw [← mul_assoc p i' i, e2, sub_mul, mul_assoc p' i i, h4, mul_neg]
      module
    rw [hc, hc']
    conv_rhs => rw [← d1]
    module
  · have hc : ((3/2 : ℝ) • (p' * p) - p' - (1/2 : ℝ) • (i' * i)) * i
        = (3/2 : ℝ) • (p' * i) - p' * i + (1/2 : ℝ) • (i' * p) := by
      simp only [sub_mul, smul_mul_assoc, mul_assoc, h3, h4, mul_neg]
      module
    have hc' : i * ((3/2 : ℝ) • (p' * p) - p' - (1/2 : ℝ) • (i' * i))
        = - i' + i' * p + (1/2 : ℝ) • (p' * i) - (1/2 : ℝ) • (i' * p) := by
      simp only [mul_sub, mul_smul_comm, e5, e3]
      rw [← mul_assoc i i' i, e4, sub_mul, mul_assoc i' i i, h4, mul_neg, neg_mul]
      module
    rw [hc, hc']
    module

section transport
variable {H : V n → ℝ} {J : V n → V n →L[ℝ] V n} (hH : IsStrictlyStarShapedLevel H)
  (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)

noncomputable def Pd (P : ReebOrbit H) (t : ℝ) : V n →L[ℝ] V n := deriv (Pr P) t
noncomputable def Id (J : V n → V n →L[ℝ] V n) (P : ReebOrbit H) (t : ℝ) : V n →L[ℝ] V n :=
  deriv (Iop J P) t

/-- the Kato generator -/
noncomputable def Cg (J : V n → V n →L[ℝ] V n) (P : ReebOrbit H) (t : ℝ) : V n →L[ℝ] V n :=
  (3/2 : ℝ) • (Pd P t * Pr P t) - Pd P t - (1/2 : ℝ) • (Id J P t * Iop J P t)

include hH in
lemma hasDerivAt_Pr (t : ℝ) : HasDerivAt (Pr P) (Pd P t) t :=
  ((Pr_smooth hH P).differentiable (by simp) t).hasDerivAt

include hH hJ in
lemma hasDerivAt_Iop (t : ℝ) : HasDerivAt (Iop J P) (Id J P t) t :=
  ((Iop_smooth hH hJ P).differentiable (by simp) t).hasDerivAt

include hH in
lemma d1 (t : ℝ) : Pd P t * Pr P t + Pr P t * Pd P t = Pd P t := by
  have h := (hasDerivAt_Pr hH P t).mul (hasDerivAt_Pr hH P t)
  have hf : (Pr P * Pr P) = Pr P := funext fun s => PP hH P s
  rw [hf] at h; exact h.unique (hasDerivAt_Pr hH P t)

include hH hJ in
lemma d2 (t : ℝ) : Id J P t * Pr P t + Iop J P t * Pd P t = Id J P t := by
  have h := (hasDerivAt_Iop hH hJ P t).mul (hasDerivAt_Pr hH P t)
  have hf : (Iop J P * Pr P) = Iop J P := funext fun s => IP hH P s
  rw [hf] at h; exact h.unique (hasDerivAt_Iop hH hJ P t)

include hH hJ in
lemma d3 (t : ℝ) : Pd P t * Iop J P t + Pr P t * Id J P t = Id J P t := by
  have h := (hasDerivAt_Pr hH P t).mul (hasDerivAt_Iop hH hJ P t)
  have hf : (Pr P * Iop J P) = Iop J P := funext fun s => PI hH hJ P s
  rw [hf] at h; exact h.unique (hasDerivAt_Iop hH hJ P t)

include hH hJ in
lemma d4 (t : ℝ) : Id J P t * Iop J P t + Iop J P t * Id J P t = - Pd P t := by
  have h := (hasDerivAt_Iop hH hJ P t).mul (hasDerivAt_Iop hH hJ P t)
  have hf : (Iop J P * Iop J P) = - Pr P := funext fun s => II hH hJ P s
  rw [hf] at h; exact h.unique (hasDerivAt_Pr hH P t).neg

include hH hJ in
lemma d5 (t : ℝ) (u w : V n) : omega0 (Id J P t u) w + omega0 u (Id J P t w) = 0 := by
  have hu : HasDerivAt (fun s => Iop J P s u) (Id J P t u) t := by
    simpa using (hasDerivAt_Iop hH hJ P t).clm_apply (hasDerivAt_const t u)
  have hw : HasDerivAt (fun s => Iop J P s w) (Id J P t w) t := by
    simpa using (hasDerivAt_Iop hH hJ P t).clm_apply (hasDerivAt_const t w)
  have h := (hasDerivAt_om hu (hasDerivAt_const t w)).add (hasDerivAt_om (hasDerivAt_const t u) hw)
  have hf : ((fun s => omega0 (Iop J P s u) w) + fun s => omega0 u (Iop J P s w)) = fun _ => (0 : ℝ) := by
    funext s; simp only [Pi.add_apply]; rw [Iop_skew hH hJ P s]; ring
  rw [hf] at h
  have := h.unique (hasDerivAt_const t (0 : ℝ))
  simpa [om_zero_left, om_zero_right] using this

include hH hJ in
lemma Cg_lax (t : ℝ) : Cg J P t * Pr P t - Pr P t * Cg J P t = Pd P t ∧
    Cg J P t * Iop J P t - Iop J P t * Cg J P t = Id J P t :=
  lax_alg _ _ _ _ (PP hH P t) (IP hH P t) (PI hH hJ P t) (II hH hJ P t) (d1 hH P t)
    (d2 hH hJ P t) (d3 hH hJ P t) (d4 hH hJ P t)

include hH hJ in
lemma Cg_smooth : ContDiff ℝ ∞ (Cg J P) := by
  have hP := Pr_smooth hH P
  have hI := Iop_smooth hH hJ P
  have hP' : ContDiff ℝ ∞ (Pd P) := (contDiff_infty_iff_deriv.1 hP).2
  have hI' : ContDiff ℝ ∞ (Id J P) := (contDiff_infty_iff_deriv.1 hI).2
  exact ((hP'.mul hP).const_smul _ |>.sub hP').sub ((hI'.mul hI).const_smul _)

lemma deriv_periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hf : ∀ t, f (t + 1) = f t) (t : ℝ) : deriv f (t + 1) = deriv f t := by
  rw [← deriv_comp_add_const]
  congr 1; funext s; exact hf s

lemma Cg_periodic (t : ℝ) : Cg J P (t + 1) = Cg J P t := by
  simp only [Cg, Pd, Id, deriv_periodic (Pr_periodic P) t, deriv_periodic (Iop_periodic J P) t,
    Pr_periodic, Iop_periodic]

include hH hJ in
lemma Cg_bound : ∃ K : NNReal, ∀ t, ‖ContinuousLinearMap.mul ℝ (V n →L[ℝ] V n) (Cg J P t)‖₊ ≤ K := by
  have hc := (Cg_smooth hH hJ P).continuous
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨Real.toNNReal K, fun t => ?_⟩
  obtain ⟨y, hy, hty⟩ := Function.Periodic.exists_mem_Ico₀ (c := (1 : ℝ))
    (fun s => Cg_periodic P s) one_pos t
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  refine (ContinuousLinearMap.opNorm_mul_apply_le ℝ _ _).trans ?_
  rw [hty]
  exact (hK y (Ico_subset_Icc_self hy)).trans (le_max_left _ _)

include hH hJ in
lemma exists_U : ∃ U : ℝ → (V n →L[ℝ] V n), U 0 = 1 ∧ ∀ t, HasDerivAt U (Cg J P t * U t) t := by
  obtain ⟨K, hK⟩ := Cg_bound hH hJ P
  obtain ⟨U, h0, hU⟩ := uf_lode_exists (F := V n →L[ℝ] V n)
    (fun t => ContinuousLinearMap.mul ℝ (V n →L[ℝ] V n) (Cg J P t))
    ((ContinuousLinearMap.mul ℝ (V n →L[ℝ] V n)).continuous.comp (Cg_smooth hH hJ P).continuous)
    K hK 1
  exact ⟨U, h0, fun t => by simpa using hU t⟩

/-- conjugation (Lax) lemma -/
lemma lax_transport {Q Q' C U : ℝ → (V n →L[ℝ] V n)} (hQ : ∀ t, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t, Q' t = C t * Q t - Q t * C t) (hU : ∀ t, HasDerivAt U (C t * U t) t)
    (hU0 : U 0 = 1) (K : NNReal) (hK : ∀ t, ‖ContinuousLinearMap.mul ℝ (V n →L[ℝ] V n) (C t)‖₊ ≤ K)
    (t : ℝ) : Q t * U t = U t * Q 0 := by
  have hR : ∀ s, HasDerivAt (fun s => Q s * U s - U s * Q 0)
      (ContinuousLinearMap.mul ℝ (V n →L[ℝ] V n) (C s) (Q s * U s - U s * Q 0)) s := by
    intro s
    have h : HasDerivAt (fun s => Q s * U s - U s * Q 0) _ s :=
      ((hQ s).mul (hU s)).sub ((hU s).mul_const (Q 0))
    refine h.congr_deriv ?_
    rw [ContinuousLinearMap.mul_apply', hQ']
    simp only [mul_sub, sub_mul, mul_assoc]
    abel
  have h0 : ∀ s, HasDerivAt (fun _ : ℝ => (0 : V n →L[ℝ] V n))
      (ContinuousLinearMap.mul ℝ (V n →L[ℝ] V n) (C s) 0) s := fun s => by
    simpa using hasDerivAt_const s (0 : V n →L[ℝ] V n)
  have := uf_lode_unique _ K hK _ _ hR h0 0 (by simp [hU0])
  exact sub_eq_zero.1 (congrFun this t)

end transport

/-! ## Properties of the transport -/

section uprops
variable {H : V n → ℝ} {J : V n → V n →L[ℝ] V n} (hH : IsStrictlyStarShapedLevel H)
  (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)

lemma mulA (f g : V n →L[ℝ] V n) (v : V n) : (f * g) v = f (g v) := rfl

lemma om_sub_right (u v v' : V n) : omega0 u (v - v') = omega0 u v - omega0 u v' := by
  simp only [← om_apply, map_sub]

include hH hJ in
lemma Cg_skew (t : ℝ) (a b : V n) (ha : IsInXi H (gam P t) a) (hb : IsInXi H (gam P t) b) :
    omega0 (Cg J P t a) b + omega0 a (Cg J P t b) = 0 := by
  have hPa : Pr P t a = a := Pr_of_xi P t a ha
  have hPb : Pr P t b = b := Pr_of_xi P t b hb
  have q : ∀ c, Pr P t c = c → Pr P t (Pd P t c) = 0 := fun c hc => by
    have := congrArg (fun L => L c) (d1 hH P t)
    simp only [ContinuousLinearMap.add_apply, mulA, hc] at this
    simpa using this
  have f2 : omega0 (Pd P t a) b = 0 := by
    have := kerP_orth hH P t (Pd P t a) b hb; rwa [q a hPa, sub_zero] at this
  have f4 : omega0 a (Pd P t b) = 0 := by
    have := kerP_orth' hH P t (Pd P t b) a ha; rwa [q b hPb, sub_zero] at this
  have f5 : omega0 (Id J P t (Iop J P t a)) b = omega0 a (Iop J P t (Id J P t b)) := by
    have h1 := d5 hH hJ P t (Iop J P t a) b
    have h2 := Iop_skew hH hJ P t a (Id J P t b)
    linarith
  have f6 : omega0 a (Id J P t (Iop J P t b)) + omega0 a (Iop J P t (Id J P t b)) = 0 := by
    have := congrArg (fun L => L b) (d4 hH hJ P t)
    simp only [ContinuousLinearMap.add_apply, mulA,
      ContinuousLinearMap.neg_apply] at this
    rw [← om_add_right, this, om_neg_right, f4, neg_zero]
  simp only [Cg, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    mulA, hPa, hPb, om_sub_left, om_sub_right, om_smul_left, om_smul_right]
  linarith

variable {U : ℝ → (V n →L[ℝ] V n)} (hU0 : U 0 = 1) (hU : ∀ t, HasDerivAt U (Cg J P t * U t) t)
include hH hJ hU0 hU

lemma U_Pr (t : ℝ) : Pr P t * U t = U t * Pr P 0 := by
  obtain ⟨K, hK⟩ := Cg_bound hH hJ P
  exact lax_transport (hasDerivAt_Pr hH P) (fun t => ((Cg_lax hH hJ P t).1).symm) hU hU0 K hK t

lemma U_Iop (t : ℝ) : Iop J P t * U t = U t * Iop J P 0 := by
  obtain ⟨K, hK⟩ := Cg_bound hH hJ P
  exact lax_transport (hasDerivAt_Iop hH hJ P) (fun t => ((Cg_lax hH hJ P t).2).symm) hU hU0 K hK t

lemma U_xi (t : ℝ) (v : V n) (hv : IsInXi H (gam P 0) v) : IsInXi H (gam P t) (U t v) := by
  have h := congrArg (fun L => L v) (U_Pr hH hJ P hU0 hU t)
  simp only [mulA, Pr_of_xi P 0 v hv] at h
  rw [← h]; exact Pr_xi hH P t _

lemma U_J (t : ℝ) (v : V n) (hv : IsInXi H (gam P 0) v) :
    J (gam P t) (U t v) = U t (J (gam P 0) v) := by
  have h := congrArg (fun L => L v) (U_Iop hH hJ P hU0 hU t)
  simp only [mulA, Iop, ContinuousLinearMap.comp_apply,
    Pr_of_xi P 0 v hv, Pr_of_xi P t _ (U_xi hH hJ P hU0 hU t v hv)] at h
  exact h

lemma U_om (t : ℝ) (v w : V n) (hv : IsInXi H (gam P 0) v) (hw : IsInXi H (gam P 0) w) :
    omega0 (U t v) (U t w) = omega0 v w := by
  have hd : ∀ s, HasDerivAt (fun s => omega0 (U s v) (U s w))
      (omega0 (Cg J P s (U s v)) (U s w) + omega0 (U s v) (Cg J P s (U s w))) s := by
    intro s
    have hv' : HasDerivAt (fun s => U s v) (Cg J P s (U s v)) s := by
      simpa using (hU s).clm_apply (hasDerivAt_const s v)
    have hw' : HasDerivAt (fun s => U s w) (Cg J P s (U s w)) s := by
      simpa using (hU s).clm_apply (hasDerivAt_const s w)
    exact hasDerivAt_om hv' hw'
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv.trans (Cg_skew hH hJ P s _ _ (U_xi hH hJ P hU0 hU s v hv)
      (U_xi hH hJ P hU0 hU s w hw))) t 0
  simpa [hU0] using hc

lemma U_shift (t : ℝ) : U (t + 1) = U t * U 1 := by
  obtain ⟨K, hK⟩ := Cg_bound hH hJ P
  have hy : ∀ s, HasDerivAt (fun t => U (t + 1))
      (ContinuousLinearMap.mul ℝ (V n →L[ℝ] V n) (Cg J P s) (U (s + 1))) s := fun s => by
    have := (hU (s + 1)).comp_add_const s 1
    rw [Cg_periodic] at this
    simpa using this
  have hz : ∀ s, HasDerivAt (fun t => U t * U 1)
      (ContinuousLinearMap.mul ℝ (V n →L[ℝ] V n) (Cg J P s) (U s * U 1)) s := fun s => by
    have := (hU s).mul_const (U 1)
    simpa [mul_assoc] using this
  have := uf_lode_unique _ K hK _ _ hy hz 0 (by simp [hU0])
  exact congrFun this t

lemma U_smooth : ContDiff ℝ ∞ U := by
  have hdiff : Differentiable ℝ U := fun t => (hU t).differentiableAt
  have hd : deriv U = fun t => Cg J P t * U t := funext fun t => (hU t).deriv
  have key : ∀ m : ℕ, ContDiff ℝ m U := by
    intro m
    induction m with
    | zero => exact contDiff_zero.2 hdiff.continuous
    | succ m ih =>
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl]
      refine contDiff_succ_iff_deriv.2 ⟨hdiff, by simp, ?_⟩
      rw [hd]
      exact ((Cg_smooth hH hJ P).of_le (by exact_mod_cast le_top)).mul ih
  exact contDiff_infty.2 key

end uprops

/-! ## Rotations of `ℝ^{2n}` in the planes `(inl k, inr k)` -/

section rot
open UFrame

noncomputable def RotL (φ : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n ⊕ Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n ⊕ Fin n) where
  toFun a := WithLp.toLp 2 (Sum.elim
    (fun k => Real.cos (φ k) * a (Sum.inl k) - Real.sin (φ k) * a (Sum.inr k))
    (fun k => Real.sin (φ k) * a (Sum.inl k) + Real.cos (φ k) * a (Sum.inr k)))
  map_add' a b := by ext i; cases i <;> simp <;> ring
  map_smul' c a := by ext i; cases i <;> simp <;> ring

noncomputable def Rot (φ : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n ⊕ Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n ⊕ Fin n) :=
  LinearMap.toContinuousLinearMap (RotL φ)

@[simp] lemma Rot_inl (φ : Fin n → ℝ) (a : EuclideanSpace ℝ (Fin n ⊕ Fin n)) (k : Fin n) :
    Rot φ a (Sum.inl k) = Real.cos (φ k) * a (Sum.inl k) - Real.sin (φ k) * a (Sum.inr k) := rfl
@[simp] lemma Rot_inr (φ : Fin n → ℝ) (a : EuclideanSpace ℝ (Fin n ⊕ Fin n)) (k : Fin n) :
    Rot φ a (Sum.inr k) = Real.sin (φ k) * a (Sum.inl k) + Real.cos (φ k) * a (Sum.inr k) := rfl

lemma Rot_J (φ : Fin n → ℝ) (a : EuclideanSpace ℝ (Fin n ⊕ Fin n)) :
    Rot φ (Jv n a) = Jv n (Rot φ a) := by
  ext i; cases i with
  | inl k => rw [Rot_inl, Jv_inl, Jv_inl, Jv_inr, Rot_inr]; ring
  | inr k => rw [Rot_inr, Jv_inr, Jv_inl, Jv_inr, Rot_inl]; ring

lemma Rot_inner (φ : Fin n → ℝ) (a b : EuclideanSpace ℝ (Fin n ⊕ Fin n)) :
    inner ℝ (Rot φ a) (Rot φ b) = inner ℝ a b := by
  simp only [inner_eq_sum, Rot_inl, Rot_inr]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination (a (Sum.inl k) * b (Sum.inl k) + a (Sum.inr k) * b (Sum.inr k)) *
    Real.sin_sq_add_cos_sq (φ k)

lemma Rot_Rot (φ ψ : Fin n → ℝ) (a : EuclideanSpace ℝ (Fin n ⊕ Fin n)) :
    Rot φ (Rot ψ a) = Rot (φ + ψ) a := by
  ext i; cases i with
  | inl k => simp only [Rot_inl, Rot_inr, Pi.add_apply, Real.cos_add, Real.sin_add]; ring
  | inr k => simp only [Rot_inl, Rot_inr, Pi.add_apply, Real.cos_add, Real.sin_add]; ring

lemma Rot_smooth (θ : Fin n → ℝ) : ContDiff ℝ ∞ (fun t : ℝ => Rot (fun k => -(t * θ k))) := by
  refine contDiff_clm_apply_iff.2 fun a => contDiff_euclidean.2 fun i => ?_
  have hc : ∀ k, ContDiff ℝ ∞ (fun t : ℝ => Real.cos (-(t * θ k))) := fun k =>
    Real.contDiff_cos.comp (contDiff_id.mul contDiff_const).neg
  have hs : ∀ k, ContDiff ℝ ∞ (fun t : ℝ => Real.sin (-(t * θ k))) := fun k =>
    Real.contDiff_sin.comp (contDiff_id.mul contDiff_const).neg
  cases i with
  | inl k => simp only [Rot_inl]; exact ((hc k).mul contDiff_const).sub ((hs k).mul contDiff_const)
  | inr k => simp only [Rot_inr]; exact ((hs k).mul contDiff_const).add ((hc k).mul contDiff_const)

end rot

/-! ## The xi subspace -/

noncomputable def xiS (H : V n → ℝ) (x : V n) : Submodule ℝ (V n) :=
  LinearMap.ker (liouvilleCLM x : V n →ₗ[ℝ] ℝ) ⊓ LinearMap.ker (fderiv ℝ H x : V n →ₗ[ℝ] ℝ)

lemma mem_xiS (H : V n → ℝ) (x v : V n) : v ∈ xiS H x ↔ IsInXi H x v := by
  simp [xiS, IsInXi, IsoSpec.liouvilleCLM_apply]

lemma finrank_xiS {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : Module.finrank ℝ (xiS H x) = n + n := by
  obtain ⟨-, h2, h3, -⟩ := reeb_spec H hH x hx
  have hpos : 0 < fderiv ℝ H x x := hH.2.2 x hx
  let Λ : V n →ₗ[ℝ] ℝ × ℝ := LinearMap.prod (liouvilleCLM x : V n →ₗ[ℝ] ℝ) (fderiv ℝ H x : V n →ₗ[ℝ] ℝ)
  have hker : LinearMap.ker Λ = xiS H x := LinearMap.ker_prod _ _
  have hsurj : Function.Surjective Λ := by
    rintro ⟨a, b⟩
    refine ⟨a • reeb H x + (b / fderiv ℝ H x x) • x, ?_⟩
    show (liouvilleCLM x (a • reeb H x + (b / fderiv ℝ H x x) • x),
      fderiv ℝ H x (a • reeb H x + (b / fderiv ℝ H x x) • x)) = (a, b)
    simp only [map_add, map_smul, smul_eq_mul, IsoSpec.liouvilleCLM_apply, h2, h3, liou_self,
      Prod.mk.injEq]
    constructor
    · ring
    · rw [mul_zero, zero_add, div_mul_cancel₀ _ hpos.ne']
  have h := LinearMap.finrank_range_add_finrank_ker Λ
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fin_fun, hker] at h
  omega

/-! ## Main construction -/

theorem main_frame {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    ∃ Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n, IsUnitaryXiFrame J P Z := by
  obtain ⟨U, hU0, hU⟩ := exists_U hH hJ P
  have hx0 := gam_mem P 0
  have hg1 : gam P 1 = gam P 0 := by simpa using gam_periodic P 0
  set J0 := J (gam P 0) with hJ0
  have hc := hJ.2 (gam P 0) hx0
  let g0 : V n →ₗ[ℝ] V n →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => omega0 u (J0 v))
    (fun u u' v => om_add_left u u' _) (fun c u v => om_smul_left c u _)
    (fun u v v' => by rw [map_add, om_add_right]) (fun c u v => by rw [map_smul, om_smul_right]; rfl)
  have hg0 : ∀ u v, g0 u v = omega0 u (J0 v) := fun u v => rfl
  have mx : ∀ v, v ∈ xiS H (gam P 0) ↔ IsInXi H (gam P 0) v := mem_xiS H _
  have hG : UFrame.Good g0 J0.toLinearMap LinearMap.id LinearMap.id (xiS H (gam P 0)) :=
    { symm := fun u hu v hv => by
        rw [mx] at hu hv
        simp only [hg0, ContinuousLinearMap.coe_coe]
        have := (hc v (J0 u) hv (hc u u hu hu).1).2.2.2
        rw [(hc u u hu hu).2.1, om_neg_right] at this
        rw [om_antisymm u (J0 v)]; linarith
      pos := fun u hu hu0 => by rw [mx] at hu; exact (hc u u hu hu).2.2.1 hu0
      JW := fun u hu => by rw [mx] at hu ⊢; exact (hc u u hu hu).1
      JJ := fun u hu => by rw [mx] at hu; exact (hc u u hu hu).2.1
      gJ := fun u hu v hv => by
        rw [mx] at hu hv
        simp only [hg0, ContinuousLinearMap.coe_coe]
        exact (hc u (J0 v) hu (hc v v hv hv).1).2.2.2
      AW := fun u hu => hu
      BW := fun u hu => hu
      adj := fun u _ v _ => rfl
      AJ := fun u _ => rfl
      BJ := fun u _ => rfl }
  have hO : UFrame.Oracle g0 J0.toLinearMap LinearMap.id LinearMap.id (xiS H (gam P 0)) := by
    intro W' hle _ _ _ hne
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hpos := hG.pos w (hle hwW) hw0
    refine ⟨(Real.sqrt (g0 w w))⁻¹ • w, W'.smul_mem _ hwW, ?_, 0, by simp, by simp⟩
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hs := Real.sq_sqrt hpos.le
    have hs0 : Real.sqrt (g0 w w) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    field_simp
    linarith
  obtain ⟨m, e, -, heW, hee, heJ, -, hspan⟩ := UFrame.nf _ hG hO
  have hrk := UFrame.finrank_eq hG heW hee heJ hspan
  rw [finrank_xiS hH _ hx0] at hrk
  obtain rfl : n = m := by omega
  -- the frame `Y0` of `ξ_{x(0)}`
  set Y0 := UFrame.frameL J0.toLinearMap e with hY0
  have Y0mem : ∀ a, IsInXi H (gam P 0) (Y0 a) := fun a => (mx _).1 (UFrame.frame_mem hG heW hee heJ a)
  have Y0J : ∀ a, J0 (Y0 a) = Y0 (UFrame.Jv n a) := UFrame.frame_J hG heW hee heJ
  have Y0g : ∀ a b, g0 (Y0 a) (Y0 b) = inner ℝ a b := UFrame.g_frame hG heW hee heJ
  have Y0c : ∀ a, UFrame.coordL g0 J0.toLinearMap e (Y0 a) = a := UFrame.coord_frame hG heW hee heJ
  have Y0s : ∀ w, IsInXi H (gam P 0) w → Y0 (UFrame.coordL g0 J0.toLinearMap e w) = w :=
    fun w hw => UFrame.frame_coord hG heW hee heJ hspan w ((mx w).2 hw)
  -- monodromy
  have U1xi : ∀ v, IsInXi H (gam P 0) v → IsInXi H (gam P 0) (U 1 v) := fun v hv => by
    have := U_xi hH hJ P hU0 hU 1 v hv; rwa [hg1] at this
  have U1J : ∀ v, IsInXi H (gam P 0) v → J0 (U 1 v) = U 1 (J0 v) := fun v hv => by
    have := U_J hH hJ P hU0 hU 1 v hv; rwa [hg1] at this
  have U1g : ∀ v w, IsInXi H (gam P 0) v → IsInXi H (gam P 0) w → g0 (U 1 v) (U 1 w) = g0 v w :=
    fun v w hv hw => by
      rw [hg0, hg0, U1J w hw, U_om hH hJ P hU0 hU 1 v (J0 w) hv (hc w w hw hw).1]
  let M : CauchyRiemannIndex.Vec n →L[ℝ] CauchyRiemannIndex.Vec n := LinearMap.toContinuousLinearMap
    ((UFrame.coordL g0 J0.toLinearMap e) ∘ₗ (U 1 : V n →ₗ[ℝ] V n) ∘ₗ Y0)
  have hYM : ∀ a, Y0 (M a) = U 1 (Y0 a) := fun a => Y0s _ (U1xi _ (Y0mem a))
  have hM : ∀ a b, inner ℝ (M a) (M b) = inner ℝ a b := fun a b => by
    rw [← Y0g, hYM, hYM, U1g _ _ (Y0mem a) (Y0mem b), Y0g]
  have hMJ : ∀ a, M (UFrame.Jv n a) = UFrame.Jv n (M a) := fun a => by
    have h : Y0 (M (UFrame.Jv n a)) = Y0 (UFrame.Jv n (M a)) := by
      rw [hYM, ← Y0J, ← U1J _ (Y0mem a), ← hYM, Y0J]
    have := congrArg (UFrame.coordL g0 J0.toLinearMap e) h
    rwa [Y0c, Y0c] at this
  obtain ⟨f, θ, hff, hfJ, hMf, -⟩ := UFrame.vec_nf M hM hMJ
  -- the adapted family
  set e' : Fin n → V n := fun k => Y0 (f k) with he'
  have he'W : ∀ k, e' k ∈ xiS H (gam P 0) := fun k => (mx _).2 (Y0mem _)
  have he'e : ∀ i j, g0 (e' i) (e' j) = if i = j then 1 else 0 := fun i j => by
    simp only [he', Y0g, hff]
  have he'J : ∀ i j, g0 (e' i) (J0.toLinearMap (e' j)) = 0 := fun i j => by
    simp only [he', ContinuousLinearMap.coe_coe, Y0J, Y0g, hfJ]
  have hUe' : ∀ k, U 1 (e' k) = Real.cos (θ k) • e' k + Real.sin (θ k) • J0 (e' k) := fun k => by
    simp only [he', ← hYM, hMf, map_add, map_smul, Y0J]
  set Y1 := UFrame.frameL J0.toLinearMap e' with hY1
  have Y1mem : ∀ a, IsInXi H (gam P 0) (Y1 a) :=
    fun a => (mx _).1 (UFrame.frame_mem hG he'W he'e he'J a)
  have Y1J : ∀ a, J0 (Y1 a) = Y1 (UFrame.Jv n a) := UFrame.frame_J hG he'W he'e he'J
  have Y1g : ∀ a b, g0 (Y1 a) (Y1 b) = inner ℝ a b := UFrame.g_frame hG he'W he'e he'J
  have Y1om : ∀ a b, omega0 (Y1 a) (Y1 b) = inner ℝ (UFrame.Jv n a) b := fun a b => by
    have h := Y1g a (UFrame.Jv n b)
    rw [← Y1J, hg0, (hc _ _ (Y1mem b) (Y1mem b)).2.1, om_neg_right] at h
    rw [UFrame.inner_Jv]; linarith
  have Y1rot : ∀ a, U 1 (Y1 a) = Y1 (Rot θ a) := fun a => by
    simp only [hY1, UFrame.frameL_apply, map_sum, map_add, map_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : IsInXi H (gam P 0) (e' k) := (mx _).1 (he'W k)
    simp only [ContinuousLinearMap.coe_coe]
    rw [← U1J _ hk, hUe', Rot_inl, Rot_inr]
    have hJJ : J0 (J0 (e' k)) = - e' k := (hc _ _ hk hk).2.1
    simp only [map_add, map_smul, hJJ]
    module
  -- the frame
  let Y1c : CauchyRiemannIndex.Vec n →L[ℝ] V n := LinearMap.toContinuousLinearMap Y1
  let Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n :=
    fun t => (U t).comp (Y1c.comp (Rot (fun k => -(t * θ k))))
  have hZ : ∀ t a, Z t a = U t (Y1 (Rot (fun k => -(t * θ k)) a)) := fun t a => rfl
  have Zxi : ∀ t a, IsInXi H (gam P t) (Z t a) := fun t a => U_xi hH hJ P hU0 hU t _ (Y1mem _)
  have Zom : ∀ t a b, omega0 (Z t a) (Z t b) = inner ℝ (UFrame.Jv n a) b := fun t a b => by
    rw [hZ, hZ, U_om hH hJ P hU0 hU t _ _ (Y1mem _) (Y1mem _), Y1om, ← Rot_J, Rot_inner]
  refine ⟨Z, ?_, ?_, fun t => ⟨fun a => Zxi t a, ?_, fun a => ?_, fun a b => Zom t a b⟩⟩
  · exact (U_smooth hH hJ P hU0 hU).clm_comp (contDiff_const.clm_comp (Rot_smooth θ))
  · intro t
    ext1 a
    rw [hZ, hZ, U_shift hH hJ P hU0 hU t, mulA, Y1rot, Rot_Rot]
    rw [show (θ + fun k => -((t + 1) * θ k)) = (fun k => -(t * θ k)) from
      funext fun k => by simp only [Pi.add_apply]; ring]
  · -- surjectivity by dimension count
    intro w hw
    let Zl : CauchyRiemannIndex.Vec n →ₗ[ℝ] V n := (Z t : CauchyRiemannIndex.Vec n →ₗ[ℝ] V n)
    have hinj : Function.Injective Zl := by
      intro a b hab
      have h0 : Z t (a - b) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hab
      have h1 : ∀ c, inner ℝ (UFrame.Jv n (a - b)) c = 0 := fun c => by
        rw [← Zom, h0, om_zero_left]
      have h2 := inner_self_eq_zero.1 (h1 (UFrame.Jv n (a - b)))
      have h3 := UFrame.Jv_Jv (a - b)
      rw [h2, map_zero] at h3
      exact sub_eq_zero.1 (neg_eq_zero.1 h3.symm)
    have hle : LinearMap.range Zl ≤ xiS H (gam P t) := by
      rintro _ ⟨a, rfl⟩; exact (mem_xiS H _ _).2 (Zxi t a)
    have hfr : Module.finrank ℝ (LinearMap.range Zl) = Module.finrank ℝ (xiS H (gam P t)) := by
      rw [LinearMap.finrank_range_of_inj hinj, finrank_xiS hH _ (gam_mem P t), finrank_euclideanSpace]
      simp
    have heq := Submodule.eq_of_le_of_finrank_eq hle hfr
    have : w ∈ LinearMap.range Zl := heq ▸ (mem_xiS H _ _).2 hw
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩
  · -- `J Z = Z J₀`
    show J (gam P t) (Z t a) = Z t (UFrame.Jv n a)
    rw [hZ, hZ, U_J hH hJ P hU0 hU t _ (Y1mem _), Y1J, Rot_J]

end FrameBridge

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    ∃ Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n, IsUnitaryXiFrame J P Z :=
  FrameBridge.main_frame hH J hJ P
