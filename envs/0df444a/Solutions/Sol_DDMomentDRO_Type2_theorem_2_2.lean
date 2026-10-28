-- Prove2me | solution 2 for DDMomentDRO.Type2.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:56:08.062231+00:00
-- url     : https://prove2.me/submissions/f430d86b-b531-4e34-8ae4-da350aeb215e

import Mathlib
import Definitions.Def_DDMomentDRO_Type2_Setting
import Theorems.Thm_LP_farkas
import Theorems.Thm_MinMax_isLeast_add_isGreatest_iff

-- carved verbatim out of submission f8a46747-fac6-4be2-86b1-8c70fc9a1933, lines 826-855

section
open Matrix DDMomentDRO.Type2

def Dset {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (x : Fin I → ℝ) : Set ℝ :=
  {d | ∃ s : ℝ, ∃ u : Fin J → ℝ, ∃ Y : Matrix (Fin J) (Fin J) ℝ,
       (∀ k, Qn x k ≤ s + u ⬝ᵥ ξ k + ((vecMulVec (ξ k - μ x) (ξ k - μ x))ᵀ * Y).trace) ∧
       d = s + u ⬝ᵥ μ x + ((Sig x)ᵀ * Y).trace}

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def LP.DualFeas (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    Set ((ι → ℝ) × (κ → ℝ)) :=
  {yz | 0 ≤ yz.1 ∧ ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j = c}

def LP.Feas (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ) : Set E :=
  {x | (∀ i, a i x ≤ b i) ∧ ∀ j, e j x = d j}

end

section
open Matrix DDMomentDRO.Type2

abbrev Kp (J : ℕ) := Unit ⊕ (Fin J ⊕ Fin J × Fin J)

noncomputable def aa {K : ℕ} (i : Fin K) : Module.Dual ℝ (Fin K → ℝ) := -LinearMap.proj i

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def aux1_T (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) :
    (ι → ℝ) × (κ → ℝ) →ₗ[ℝ] Module.Dual ℝ E where
  toFun yz := ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

lemma aux1_alt (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty) (t : ℝ)
    (h : ∀ x ∈ LP.Feas a b e d, c x < t) :
    ∃ yz ∈ LP.DualFeas a e c, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d < t := by
  classical
  let a' : Option ι → Module.Dual ℝ E := fun o => o.elim (-c) a
  let b' : Option ι → ℝ := fun o => o.elim (-t) b
  have hinf : ¬ ∃ x : E, (∀ i, a' i x ≤ b' i) ∧ ∀ j, e j x = d j := by
    rintro ⟨x, hx1, hx2⟩
    have h1 := h x ⟨fun i => hx1 (some i), hx2⟩
    have h2 := hx1 none
    simp only [a', b', Option.elim, LinearMap.neg_apply] at h2
    linarith
  obtain ⟨y', z, hy', hsum, hneg⟩ := (LP.farkas a' b' e d).1 hinf
  rw [Fintype.sum_option] at hsum
  simp only [dotProduct, Fintype.sum_option] at hneg
  simp only [a', b', Option.elim, smul_neg] at hsum hneg
  have hy0 : 0 ≤ y' none := hy' none
  rcases hy0.eq_or_lt with h0 | h0
  · exfalso
    obtain ⟨x0, hx0⟩ := hP
    refine (LP.farkas a b e d).2 ⟨fun i => y' (some i), z, fun i => hy' (some i), ?_, ?_⟩
      ⟨x0, hx0⟩
    · rw [← h0] at hsum; simpa using hsum
    · simp only [dotProduct]; rw [← h0] at hneg; simpa using hneg
  · refine ⟨(fun i => y' (some i) / y' none, fun j => z j / y' none),
      ⟨fun i => div_nonneg (hy' _) h0.le, ?_⟩, ?_⟩
    · have hAB : ∑ i, y' (some i) • a i + ∑ j, z j • e j = y' none • c := by
        rw [← sub_eq_zero, ← hsum]; abel
      show ∑ i, (y' (some i) / y' none) • a i + ∑ j, (z j / y' none) • e j = c
      have hr : ∀ (r : ℝ) (φ : Module.Dual ℝ E), (r / y' none) • φ = (y' none)⁻¹ • (r • φ) :=
        fun r φ => by rw [smul_smul, div_eq_inv_mul]
      simp only [hr]
      rw [← Finset.smul_sum, ← Finset.smul_sum, ← smul_add, hAB, smul_smul,
        inv_mul_cancel₀ h0.ne', one_smul]
    · simp only [dotProduct]
      have : ∑ i, y' (some i) / y' none * b i + ∑ j, z j / y' none * d j =
          (∑ i, y' (some i) * b i + ∑ j, z j * d j) / y' none := by
        rw [add_div, Finset.sum_div, Finset.sum_div]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this, div_lt_iff₀ h0]
      linarith

theorem LP.weak_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) {x : E} (hx : x ∈ LP.Feas a b e d)
    {yz : (ι → ℝ) × (κ → ℝ)} (hyz : yz ∈ LP.DualFeas a e c) :
    c x ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d := by
  obtain ⟨hax, hex⟩ := hx
  obtain ⟨hy, hsum⟩ := hyz
  have h := congrArg (fun φ : Module.Dual ℝ E => φ x) hsum
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hex] at h
  have hle : ∑ i, yz.1 i * a i x ≤ ∑ i, yz.1 i * b i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hax i) (hy i)
  simp only [dotProduct]
  linarith

lemma aux1_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) :
    ∃ x ∈ LP.Feas a b e d, ∀ x' ∈ LP.Feas a b e d, c x' ≤ c x := by
  by_contra hno
  push Not at hno
  have hlt : ∀ x ∈ LP.Feas a b e d, c x < sSup (c '' LP.Feas a b e d) := fun x hx => by
    obtain ⟨x', hx', hlt⟩ := hno x hx
    exact lt_of_lt_of_le hlt (le_csSup hb ⟨x', hx', rfl⟩)
  obtain ⟨yz, hyz, hobj⟩ := aux1_alt a b e d c hP _ hlt
  have : sSup (c '' LP.Feas a b e d) ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d :=
    csSup_le (hP.image c) (by rintro _ ⟨x, hx, rfl⟩; exact LP.weak_duality a b e d c hx hyz)
  linarith

lemma aux1_dualFeas_eq (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    LP.DualFeas a e c =
      LP.Feas (fun i => -(LinearMap.proj i ∘ₗ LinearMap.fst ℝ (ι → ℝ) (κ → ℝ))) 0
        (fun k => Module.Dual.eval ℝ E (Module.finBasis ℝ E k) ∘ₗ aux1_T a e)
        (fun k => c (Module.finBasis ℝ E k)) := by
  ext yz
  simp only [LP.DualFeas, LP.Feas, Set.mem_setOf_eq, LinearMap.neg_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_fst, LinearMap.coe_proj, Function.eval, Pi.zero_apply,
    neg_nonpos, Module.Dual.eval_apply]
  constructor
  · rintro ⟨hy, hsum⟩
    exact ⟨fun i => hy i, fun k => by rw [← hsum]; rfl⟩
  · rintro ⟨hy, hk⟩
    refine ⟨fun i => hy i, ?_⟩
    have : aux1_T a e yz = c := (Module.finBasis ℝ E).ext fun k => hk k
    exact this

def aux1_obj (b : ι → ℝ) (d : κ → ℝ) : Module.Dual ℝ ((ι → ℝ) × (κ → ℝ)) where
  toFun yz := yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct]; ring
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring

lemma aux1_dual_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E)
    (d : κ → ℝ) (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ yz ∈ LP.DualFeas a e c, ∀ yz' ∈ LP.DualFeas a e c,
      yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ yz'.1 ⬝ᵥ b + yz'.2 ⬝ᵥ d := by
  obtain ⟨x0, hx0⟩ := hP
  rw [aux1_dualFeas_eq] at hD ⊢
  obtain ⟨yz, hyz, hmax⟩ := aux1_attain _ _ _ _ (-aux1_obj b d) hD (by
    refine ⟨-c x0, ?_⟩
    rintro _ ⟨yz', hyz', rfl⟩
    rw [← aux1_dualFeas_eq] at hyz'
    have := LP.weak_duality a b e d c hx0 hyz'
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    exact this)
  refine ⟨yz, hyz, fun yz' hyz' => ?_⟩
  have := hmax yz' hyz'
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  exact this

end

section
open Matrix DDMomentDRO.Type2

def dv {J : ℕ} (m : Fin J → ℝ) (Sg : Matrix (Fin J) (Fin J) ℝ) : Kp J → ℝ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl j) => m j
  | Sum.inr (Sum.inr ij) => Sg ij.1 ij.2

lemma trace_transpose_mul {J : ℕ} (M Y : Matrix (Fin J) (Fin J) ℝ) :
    (Mᵀ * Y).trace = ∑ i, ∑ j, M i j * Y i j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

def zOf {J : ℕ} (s : ℝ) (u : Fin J → ℝ) (Y : Matrix (Fin J) (Fin J) ℝ) : Kp J → ℝ :=
  Sum.elim (fun _ => s) (Sum.elim u (fun ij => Y ij.1 ij.2))

lemma dot_dv {J : ℕ} (m : Fin J → ℝ) (Sg : Matrix (Fin J) (Fin J) ℝ) (s : ℝ) (u : Fin J → ℝ)
    (Y : Matrix (Fin J) (Fin J) ℝ) :
    zOf s u Y ⬝ᵥ dv m Sg = s + u ⬝ᵥ m + (Sgᵀ * Y).trace := by
  rw [trace_transpose_mul, dotProduct, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp only [zOf, dv, Sum.elim_inl, Sum.elim_inr, dotProduct,
    Finset.univ_unique, Finset.sum_singleton, mul_one, add_assoc]
  congr 1; congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def ew {J K : ℕ} (ξ : Fin K → Fin J → ℝ) (m : Fin J → ℝ) : Kp J → Fin K → ℝ
  | Sum.inl _ => fun _ => 1
  | Sum.inr (Sum.inl j) => fun k => ξ k j
  | Sum.inr (Sum.inr ij) => fun k => (ξ k - m) ij.1 * (ξ k - m) ij.2

noncomputable def lin {K : ℕ} (w : Fin K → ℝ) : Module.Dual ℝ (Fin K → ℝ) :=
  ∑ k, w k • LinearMap.proj k

noncomputable def ee {J K : ℕ} (ξ : Fin K → Fin J → ℝ) (m : Fin J → ℝ) (j : Kp J) :
    Module.Dual ℝ (Fin K → ℝ) := lin (ew ξ m j)

lemma lin_apply {K : ℕ} (w p : Fin K → ℝ) : lin w p = ∑ k, w k * p k := by
  simp [lin, LinearMap.sum_apply]

lemma lhs_apply {J K : ℕ} (ξ : Fin K → Fin J → ℝ) (m : Fin J → ℝ) (y : Fin K → ℝ)
    (z : Kp J → ℝ) (p : Fin K → ℝ) :
    (∑ i, y i • aa i + ∑ j, z j • ee ξ m j) p = ∑ k, (-y k + ∑ j, z j * ew ξ m j k) * p k := by
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, aa, ee,
    lin_apply, LinearMap.neg_apply, LinearMap.proj_apply, smul_eq_mul, Finset.mul_sum, add_mul,
    Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma dualFeas_iff {J K : ℕ} (ξ : Fin K → Fin J → ℝ) (m : Fin J → ℝ) (Q : Fin K → ℝ)
    (y : Fin K → ℝ) (z : Kp J → ℝ) :
    (y, z) ∈ LP.DualFeas aa (ee ξ m) (lin Q) ↔
      0 ≤ y ∧ ∀ k, -y k + ∑ j, z j * ew ξ m j k = Q k := by
  unfold LP.DualFeas
  simp only [Set.mem_ofPred_eq]
  refine and_congr Iff.rfl ⟨fun h k => ?_, fun h => ?_⟩
  · have := congrArg (fun f : Module.Dual ℝ (Fin K → ℝ) => f (Pi.single k 1)) h
    simp only [lhs_apply, lin_apply] at this
    simpa [Pi.single_apply] using this
  · apply LinearMap.ext; intro p
    rw [lhs_apply, lin_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [h k]

lemma feas_iff {I J K : ℕ} (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (x : Fin I → ℝ) (p : Fin K → ℝ) :
    p ∈ LP.Feas aa (0 : Fin K → ℝ) (ee ξ (μ x)) (dv (μ x) (Sig x)) ↔
      p ∈ amb2 ξ μ Sig x := by
  unfold LP.Feas amb2
  simp only [Set.mem_ofPred_eq, aa, ee, lin_apply, LinearMap.neg_apply, LinearMap.proj_apply,
    Pi.zero_apply, neg_nonpos, Sum.forall, ew, dv, one_mul, Prod.forall]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨?_, ?_, ?_, h0⟩
    · simpa using h1
    · funext j; rw [← h2 j]; simp [Finset.sum_apply, mul_comm]
    · ext i j; rw [← h3 i j, Matrix.sum_apply]
      exact Finset.sum_congr rfl fun k _ => by simp [vecMulVec_apply]; ring
  · rintro ⟨h1, h2, h3, h0⟩
    refine ⟨h0, ?_, ?_, ?_⟩
    · simpa using h1
    · intro j; rw [← h2]; simp [Finset.sum_apply, mul_comm]
    · intro i j; rw [← h3, Matrix.sum_apply]
      exact Finset.sum_congr rfl fun k _ => by simp [vecMulVec_apply]; ring

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem LP.strong_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ v : ℝ, IsGreatest (c '' LP.Feas a b e d) v ∧
      IsLeast ((fun yz => yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d) '' LP.DualFeas a e c) v := by
  obtain ⟨yz, hyz, hmin⟩ := aux1_dual_attain a b e d c hP hD
  obtain ⟨x, hx, hxw⟩ : ∃ x ∈ LP.Feas a b e d, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ c x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨yz', hyz', hlt⟩ := aux1_alt a b e d c hP _ hcon
    linarith [hmin yz' hyz']
  refine ⟨yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d,
    ⟨⟨x, hx, le_antisymm (LP.weak_duality a b e d c hx hyz) hxw⟩, ?_⟩,
    ⟨⟨yz, hyz, rfl⟩, ?_⟩⟩
  · rintro _ ⟨x', hx', rfl⟩; exact LP.weak_duality a b e d c hx' hyz
  · rintro _ ⟨yz', hyz', rfl⟩; exact hmin yz' hyz'

end

section
open Matrix DDMomentDRO.Type2

lemma sum_ew {J K : ℕ} (ξ : Fin K → Fin J → ℝ) (m : Fin J → ℝ) (s : ℝ) (u : Fin J → ℝ)
    (Y : Matrix (Fin J) (Fin J) ℝ) (k : Fin K) :
    ∑ t, zOf s u Y t * ew ξ m t k =
      s + u ⬝ᵥ ξ k + ((vecMulVec (ξ k - m) (ξ k - m))ᵀ * Y).trace := by
  rw [trace_transpose_mul, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [zOf, ew, Sum.elim_inl, Sum.elim_inr, vecMulVec_apply, dotProduct,
    Finset.univ_unique, Finset.sum_singleton, mul_one, add_assoc]
  congr 1; congr 1
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma z_eq_zOf {J : ℕ} (z : Kp J → ℝ) :
    z = zOf (z (Sum.inl ())) (fun j => z (Sum.inr (Sum.inl j)))
      (Matrix.of fun i j => z (Sum.inr (Sum.inr (i, j)))) := by
  funext t
  rcases t with ⟨⟩ | t | ⟨i, j⟩ <;> rfl

lemma pointwise {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (x : Fin I → ℝ) (hne : (amb2 ξ μ Sig x).Nonempty) :
    ∃ w, IsGreatest (wcVal Qn ξ μ Sig x) w ∧ IsLeast (Dset Qn ξ μ Sig x) w := by
  have hP : (LP.Feas aa (0 : Fin K → ℝ) (ee ξ (μ x)) (dv (μ x) (Sig x))).Nonempty := by
    obtain ⟨p, hp⟩ := hne; exact ⟨p, (feas_iff ξ μ Sig x p).2 hp⟩
  have hD : (LP.DualFeas aa (ee ξ (μ x)) (lin (Qn x))).Nonempty := by
    set s := ∑ k, |Qn x k|
    refine ⟨(fun k => s - Qn x k, zOf s 0 0), (dualFeas_iff _ _ _ _ _).2 ⟨fun k => ?_, fun k => ?_⟩⟩
    · have : |Qn x k| ≤ s :=
        Finset.single_le_sum (f := fun k => |Qn x k|) (fun i _ => abs_nonneg _) (Finset.mem_univ k)
      have := le_abs_self (Qn x k)
      simp only [Pi.zero_apply]; linarith
    · rw [sum_ew]; simp
  obtain ⟨v, hG, hL⟩ := LP.strong_duality aa 0 (ee ξ (μ x)) (dv (μ x) (Sig x))
    (lin (Qn x)) hP hD
  have e1 : lin (Qn x) '' LP.Feas aa (0 : Fin K → ℝ) (ee ξ (μ x)) (dv (μ x) (Sig x)) =
      wcVal Qn ξ μ Sig x := by
    ext v; constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, (feas_iff ξ μ Sig x p).1 hp, by
        rw [lin_apply]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, (feas_iff ξ μ Sig x p).2 hp, by
        rw [lin_apply]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _⟩
  have e2 : (fun yz : (Fin K → ℝ) × (Kp J → ℝ) => yz.1 ⬝ᵥ (0 : Fin K → ℝ) + yz.2 ⬝ᵥ dv (μ x) (Sig x)) ''
      LP.DualFeas aa (ee ξ (μ x)) (lin (Qn x)) = Dset Qn ξ μ Sig x := by
    ext v; constructor
    · rintro ⟨⟨y, z⟩, hyz, rfl⟩
      rw [dualFeas_iff] at hyz
      obtain ⟨hy, hk⟩ := hyz
      rw [z_eq_zOf z] at hk ⊢
      refine ⟨z (Sum.inl ()), fun j => z (Sum.inr (Sum.inl j)),
        Matrix.of fun i j => z (Sum.inr (Sum.inr (i, j))), fun k => ?_, ?_⟩
      · have := hk k; rw [sum_ew] at this
        have := hy k; simp only [Pi.zero_apply] at this; linarith
      · simp only [dotProduct_zero, zero_add]; rw [dot_dv]
    · rintro ⟨s, u, Y, hk, rfl⟩
      refine ⟨(fun k => s + u ⬝ᵥ ξ k + ((vecMulVec (ξ k - μ x) (ξ k - μ x))ᵀ * Y).trace - Qn x k,
        zOf s u Y), (dualFeas_iff _ _ _ _ _).2 ⟨fun k => ?_, fun k => ?_⟩, ?_⟩
      · have := hk k; simp only [Pi.zero_apply]; linarith
      · rw [sum_ew]; ring
      · simp only [dotProduct_zero, zero_add]; rw [dot_dv]
  rw [e1] at hG; rw [e2] at hL
  exact ⟨v, hG, hL⟩

end

section

open DDMomentDRO.Type2 in
theorem solution {I J K : ℕ}
    (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ) (Qn : (Fin I → ℝ) → Fin K → ℝ)
    (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (hbin : ∀ z ∈ S, ∀ i, z.1 i = 0 ∨ z.1 i = 1)
    (hne : ∀ x y, (x, y) ∈ S → (amb2 ξ μ Sig x).Nonempty) :
    ∀ q : ℝ,
      IsLeast (stageVals S g Qn ξ μ Sig) q ↔ IsLeast (dualVals2 S g Qn ξ μ Sig) q := by
  intro q
  have key := MinMax.isLeast_add_isGreatest_iff S (fun z => g z.1 z.2)
    (fun z => wcVal Qn ξ μ Sig z.1) (fun z => Dset Qn ξ μ Sig z.1)
    (fun z hz => pointwise Qn ξ μ Sig z.1 (hne z.1 z.2 hz)) q
  have h1 : stageVals S g Qn ξ μ Sig =
      {v | ∃ z ∈ S, ∃ w, IsGreatest (wcVal Qn ξ μ Sig z.1) w ∧ v = g z.1 z.2 + w} := by
    ext v; constructor
    · rintro ⟨x, y, w, hS, hw, rfl⟩; exact ⟨(x, y), hS, w, hw, rfl⟩
    · rintro ⟨⟨x, y⟩, hS, w, hw, rfl⟩; exact ⟨x, y, w, hS, hw, rfl⟩
  have h2 : dualVals2 S g Qn ξ μ Sig =
      {v | ∃ z ∈ S, ∃ d ∈ Dset Qn ξ μ Sig z.1,
        v = g z.1 z.2 + d} := by
    ext v; constructor
    · rintro ⟨x, y, s, u, Y, hS, hk, rfl⟩
      exact ⟨(x, y), hS, _, ⟨s, u, Y, hk, rfl⟩, by simp only; ring⟩
    · rintro ⟨⟨x, y⟩, hS, _, ⟨s, u, Y, hk, rfl⟩, rfl⟩
      exact ⟨x, y, s, u, Y, hS, hk, by ring⟩
  rw [h1, h2]; exact key

end
