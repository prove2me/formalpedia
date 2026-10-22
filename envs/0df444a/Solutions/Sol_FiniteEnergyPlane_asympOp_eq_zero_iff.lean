-- Prove2me | solution 1 for FiniteEnergyPlane.asympOp_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:35:13.080069+00:00
-- url     : https://prove2.me/submissions/ea475f5f-dda9-4890-ab14-1134f141849b

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

section lode
open Set Filter Topology
open scoped NNReal
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma g71s_lode_local (B : ℝ → F →L[ℝ] F) (hB : Continuous B) (K : ℝ≥0)
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

lemma g71s_piece {y g : ℝ → F} {S : Set ℝ} (hS : IsClosed S) (B : ℝ → F →L[ℝ] F)
    (heq : EqOn y g S) (hg : ∀ t ∈ S, HasDerivWithinAt g (B t (g t)) S t) (t : ℝ) :
    HasDerivWithinAt y (B t (y t)) S t := by
  by_cases ht : t ∈ S
  · rw [heq ht]; exact (hg t ht).congr (fun x hx => heq hx) (heq ht)
  · exact hasDerivWithinAt_iff_hasFDerivWithinAt.2
      (HasFDerivWithinAt.of_notMem_closure (by rwa [hS.closure_eq]))

lemma g71s_lode_steps (B : ℝ → F →L[ℝ] F) (hB : Continuous B) (K : ℝ≥0)
    (hK : ∀ t, ‖B t‖₊ ≤ K) (h : ℝ) (hh : 0 < h) (hKh : 2 * (K:ℝ) * h ≤ 1) (x₀ : F) (N : ℕ) :
    ∃ y : ℝ → F, y 0 = x₀ ∧ ∀ t ∈ Icc (-((N+1) * h)) ((N+1) * h),
      HasDerivWithinAt y (B t (y t)) (Icc (-((N+1) * h)) ((N+1) * h)) t := by
  induction N with
  | zero =>
    obtain ⟨y, hy0, hy⟩ := g71s_lode_local B hB K hK h hh hKh 0 x₀
    refine ⟨y, hy0, ?_⟩
    simpa using hy
  | succ N ih =>
    obtain ⟨y, hy0, hy⟩ := ih
    set c : ℝ := (N + 1) * h with hc
    have hc0 : 0 < c := by positivity
    obtain ⟨u, hu0, hu⟩ := g71s_lode_local B hB K hK h hh hKh c (y c)
    obtain ⟨w, hw0, hw⟩ := g71s_lode_local B hB K hK h hh hKh (-c) (y (-c))
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
    · refine g71s_piece isClosed_Icc B (g := w) ?_ ?_ t
      · intro s hs
        simp only [z]
        rcases eq_or_lt_of_le hs.2 with h1 | h1
        · rw [if_neg (by linarith), if_neg (by linarith), h1, hw0]
        · rw [if_neg (by linarith), if_pos h1]
      · intro s hs
        exact (hw s ⟨by linarith [hs.1], by linarith [hs.2]⟩).mono
          (Icc_subset_Icc (by linarith) (by linarith))
    · refine g71s_piece isClosed_Icc B (g := y) ?_ ?_ t
      · intro s hs
        simp only [z]; rw [if_neg (by linarith [hs.2]), if_neg (by linarith [hs.1])]
      · intro s hs; exact hy s hs
    · refine g71s_piece isClosed_Icc B (g := u) ?_ ?_ t
      · intro s hs
        simp only [z]
        rcases eq_or_lt_of_le hs.1 with h1 | h1
        · rw [if_neg (by linarith), if_neg (by linarith), ← h1, hu0]
        · rw [if_pos h1]
      · intro s hs
        exact (hu s ⟨by linarith [hs.1], by linarith [hs.2]⟩).mono
          (Icc_subset_Icc (by linarith) (by linarith))

lemma g71s_lode_exists (B : ℝ → F →L[ℝ] F) (hB : Continuous B) (K : ℝ≥0)
    (hK : ∀ t, ‖B t‖₊ ≤ K) (x₀ : F) :
    ∃ y : ℝ → F, y 0 = x₀ ∧ ∀ t, HasDerivAt y (B t (y t)) t := by
  set h : ℝ := 1 / (2 * (K:ℝ) + 1) with hhdef
  have hh : 0 < h := by positivity
  have hKh : 2 * (K:ℝ) * h ≤ 1 := by
    rw [hhdef, mul_one_div, div_le_one (by positivity)]; linarith
  choose Ψ hΨ0 hΨ using g71s_lode_steps B hB K hK h hh hKh x₀
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

lemma g71s_lode_unique (B : ℝ → F →L[ℝ] F) (K : ℝ≥0) (hK : ∀ t, ‖B t‖₊ ≤ K)
    (y z : ℝ → F) (hy : ∀ t, HasDerivAt y (B t (y t)) t) (hz : ∀ t, HasDerivAt z (B t (z t)) t)
    (t₀ : ℝ) (h0 : y t₀ = z t₀) : y = z :=
  ODE_solution_unique_univ (K := K) (v := fun t => (B t : F → F)) (s := fun _ => (univ : Set F))
    (fun t => ((B t).lipschitz.weaken (hK t)).lipschitzOnWith)
    (fun t => ⟨hy t, trivial⟩) (fun t => ⟨hz t, trivial⟩) h0

end lode

variable {n : ℕ}

lemma g71s_j0_add (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [j0, Pi.add_apply]; split_ifs <;> ring

lemma g71s_j0_smul (c : ℝ) (u : V n) : j0 (c • u) = c • j0 u := by
  funext k; simp only [j0, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

noncomputable def g71s_j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := g71s_j0_add, map_smul' := g71s_j0_smul }

@[simp] lemma g71s_j0L_apply (u : V n) : (g71s_j0L : V n →L[ℝ] V n) u = j0 u := rfl

lemma g71s_j0_j0 (u : V n) : j0 (j0 u) = -u := by
  funext k
  simp only [j0, Pi.neg_apply]
  by_cases h : (k:ℕ) % 2 = 0
  · have h1 : ¬ ((k:ℕ) + 1) % 2 = 0 := by omega
    rw [dif_pos h]
    simp only [dif_neg h1]
    congr 2
  · have h1 : ((k:ℕ) - 1) % 2 = 0 := by omega
    rw [dif_neg h]
    simp only [dif_pos h1]
    congr 2; ext; simp; omega

lemma g71s_dot_comm (u v : V n) : dot u v = dot v u := by
  simp only [dot]; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

lemma g71s_dot_add_right (u v w : V n) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma g71s_dot_smul_right (c : ℝ) (u v : V n) : dot u (c • v) = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)

lemma g71s_dot_neg_left (u v : V n) : dot (-u) v = - dot u v := by
  simp only [dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

lemma g71s_dot_j0_skew (u v : V n) : dot (j0 u) v = - dot u (j0 v) := by
  rw [eq_neg_iff_add_eq_zero]
  simp only [dot, ← Finset.sum_add_distrib]
  let σ : Fin (2 * (n + 1)) → Fin (2 * (n + 1)) := fun k =>
    if h : (k:ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩
  refine Finset.sum_involution (fun k _ => σ k) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
  · intro k _
    by_cases h : (k:ℕ) % 2 = 0
    · have h1 : ¬ ((k:ℕ) + 1) % 2 = 0 := by omega
      simp only [σ, j0, dif_pos h, Fin.val_mk, dif_neg h1]
      have e : (⟨(k:ℕ) + 1 - 1, by omega⟩ : Fin (2 * (n + 1))) = k := by ext; simp
      rw [e]; ring
    · have h1 : ((k:ℕ) - 1) % 2 = 0 := by omega
      simp only [σ, j0, dif_neg h, Fin.val_mk, dif_pos h1]
      have e : (⟨(k:ℕ) - 1 + 1, by omega⟩ : Fin (2 * (n + 1))) = k := by ext; simp; omega
      rw [e]; ring
  · intro k _ _ hk
    by_cases h : (k:ℕ) % 2 = 0 <;> simp [σ, h, Fin.ext_iff] at hk <;> omega
  · intro k _
    simp only [σ]
    by_cases h : (k:ℕ) % 2 = 0
    · have h1 : ¬ ((k:ℕ) + 1) % 2 = 0 := by omega
      simp only [dif_pos h, Fin.val_mk, dif_neg h1]; ext; simp
    · have h1 : ((k:ℕ) - 1) % 2 = 0 := by omega
      simp only [dif_neg h, Fin.val_mk, dif_pos h1]; ext; simp; omega

lemma g71s_omega_skew (u v : V n) : omega0 u v = - omega0 v u := by
  simp only [omega0]; rw [g71s_dot_j0_skew, g71s_dot_comm]

lemma g71s_omega_j0_left (g w : V n) : omega0 (j0 g) w = - dot g w := by
  simp only [omega0, g71s_j0_j0, g71s_dot_neg_left]

lemma g71s_omega_j0_right (g w : V n) : omega0 w (j0 g) = dot w g := by
  simp only [omega0]; rw [g71s_dot_j0_skew, g71s_j0_j0]
  simp only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg]

lemma g71s_clm_eq_dot (L : V n →L[ℝ] ℝ) (w : V n) :
    L w = dot (fun k => L (Pi.single k 1)) w := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]; simp only [dot]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (Pi.single k (w k) : V n) = w k • Pi.single k (1:ℝ) by
    rw [← Pi.single_smul]; simp]
  rw [map_smul, smul_eq_mul, mul_comm]

lemma g71s_fderiv_eq_dot_grad (H : V n → ℝ) (y w : V n) : fderiv ℝ H y w = dot (grad H y) w :=
  g71s_clm_eq_dot _ _

/-- bilinear forms -/
noncomputable def g71s_dotB : V n →L[ℝ] V n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V n →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V n →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ dot
        (fun a b c => by simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib])
        (fun c a b => by simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring))
        (fun a b c => g71s_dot_add_right a b c)
        (fun c a b => g71s_dot_smul_right c a b))

@[simp] lemma g71s_dotB_apply (u v : V n) : (g71s_dotB : V n →L[ℝ] V n →L[ℝ] ℝ) u v = dot u v := rfl

noncomputable def g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ := g71s_dotB.comp g71s_j0L

@[simp] lemma g71s_omB_apply (u v : V n) : (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ) u v = omega0 u v := rfl

/-! geometry -/

lemma g71s_dot_self_j0 (g : V n) : dot g (j0 g) = 0 := by
  have h := g71s_dot_j0_skew g g
  rw [g71s_dot_comm] at h; linarith

lemma g71s_liouville_ham (H : V n → ℝ) (y : V n) :
    liouville y (hamVF H y) = fderiv ℝ H y y / 2 := by
  simp only [liouville, hamVF, g71s_omega_j0_right, g71s_fderiv_eq_dot_grad, g71s_dot_comm]

lemma g71s_reeb_eq (H : V n → ℝ) (y : V n) :
    reeb H y = (fderiv ℝ H y y / 2)⁻¹ • j0 (grad H y) := by
  show (liouville y (hamVF H y))⁻¹ • hamVF H y = _
  rw [g71s_liouville_ham]; rfl

lemma g71s_contDiff_grad {H : V n → ℝ} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (grad H) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  exact contDiff_pi.2 (fun k => h1.clm_apply contDiff_const)

lemma g71s_contDiff_F {H : V n → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ H y y / 2) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  exact (h1.clm_apply contDiff_id).div_const _

lemma g71s_reeb_contDiffAt {H : V n → ℝ} (hH : ContDiff ℝ ∞ H) {x : V n}
    (hx : fderiv ℝ H x x ≠ 0) : ContDiffAt ℝ ∞ (reeb H) x := by
  have e : reeb H = fun y => (fderiv ℝ H y y / 2)⁻¹ • g71s_j0L (grad H y) := by
    funext y; rw [g71s_reeb_eq]; rfl
  rw [e]
  refine ContDiffAt.smul (𝕜' := ℝ) ?_ ((g71s_j0L.contDiff.comp (g71s_contDiff_grad hH)).contDiffAt)
  exact ((g71s_contDiff_F hH).contDiffAt).inv (by simpa using hx)

lemma g71s_dH_reeb (H : V n → ℝ) (y : V n) : fderiv ℝ H y (reeb H y) = 0 := by
  rw [g71s_reeb_eq, map_smul, g71s_fderiv_eq_dot_grad H y (j0 _), g71s_dot_self_j0, smul_zero]

lemma g71s_omega_smul_left (c : ℝ) (u v : V n) : omega0 (c • u) v = c * omega0 u v := by
  rw [← g71s_omB_apply, map_smul]; rfl

lemma g71s_omega_reeb_left (H : V n → ℝ) (y w : V n) :
    omega0 (reeb H y) w = -(fderiv ℝ H y y / 2)⁻¹ * fderiv ℝ H y w := by
  rw [g71s_reeb_eq, g71s_omega_smul_left, g71s_omega_j0_left, g71s_fderiv_eq_dot_grad H y w]; ring

lemma g71s_liouville_reeb (H : V n → ℝ) (y : V n) :
    liouville y (reeb H y) = (fderiv ℝ H y y / 2)⁻¹ * (fderiv ℝ H y y / 2) := by
  rw [reeb, liouville, ← g71s_omB_apply, map_smul, g71s_omB_apply, smul_eq_mul, mul_div_assoc,
    ← liouville, g71s_liouville_ham]

section geo
variable {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n} (hx : H x = 1)
include hH hx

lemma g71s_F_pos : 0 < fderiv ℝ H x x / 2 := by have := hH.2.2 x hx; linarith

lemma g71s_reeb_hasFDerivAt : HasFDerivAt (reeb H) (fderiv ℝ (reeb H) x) x :=
  ((g71s_reeb_contDiffAt hH.1 (by have := g71s_F_pos hH hx; intro h; rw [h] at this; norm_num at this)).differentiableAt (by simp)).hasFDerivAt

lemma g71s_hD : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) x) x :=
  ((hH.1.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt

lemma g71s_F_ne : fderiv ℝ H x x / 2 ≠ 0 := (g71s_F_pos hH hx).ne'

lemma g71s_sym (v w : V n) :
    fderiv ℝ (fderiv ℝ H) x v w = fderiv ℝ (fderiv ℝ H) x w v :=
  (hH.1.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.2 le_top)) v w

lemma g71s_dH_R' (v : V n) :
    fderiv ℝ H x (fderiv ℝ (reeb H) x v) = - fderiv ℝ (fderiv ℝ H) x v (reeb H x) := by
  have h1 := (g71s_hD hH hx).clm_apply (g71s_reeb_hasFDerivAt hH hx)
  have h0 : HasFDerivAt (fun y => fderiv ℝ H y (reeb H y)) (0 : V n →L[ℝ] ℝ) x := by
    simp only [g71s_dH_reeb]; exact hasFDerivAt_const 0 x
  have := congrArg (fun L => L v) (h1.unique h0)
  simp at this; linarith

lemma g71s_om_R' (v : V n) :
    omega0 x (fderiv ℝ (reeb H) x v) = - omega0 v (reeb H x) := by
  have h1 := (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).hasFDerivAt_of_bilinear (hasFDerivAt_id x)
    (g71s_reeb_hasFDerivAt hH hx)
  have hev : ∀ᶠ y in 𝓝 x, fderiv ℝ H y y / 2 ≠ 0 :=
    (g71s_contDiff_F hH.1).continuous.continuousAt.eventually_ne (g71s_F_ne hH hx)
  have h0 : HasFDerivAt (fun y => (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ) (id y) (reeb H y))
      (0 : V n →L[ℝ] ℝ) x := by
    refine (hasFDerivAt_const (2:ℝ) x).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    have := g71s_liouville_reeb H y
    rw [inv_mul_cancel₀ hy] at this
    simp only [id, g71s_omB_apply]; unfold liouville at this; linarith
  have := congrArg (fun L => L v) (h1.unique h0)
  simp at this; linarith

lemma g71s_om_R'_left (v w : V n) (hw : fderiv ℝ H x w = 0) :
    omega0 (fderiv ℝ (reeb H) x v) w =
      -(fderiv ℝ H x x / 2)⁻¹ * fderiv ℝ (fderiv ℝ H) x v w := by
  have h1 : HasFDerivAt (fun y => ((g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).flip w) (reeb H y))
      (((g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).flip w).comp (fderiv ℝ (reeb H) x)) x :=
    ((g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).flip w).hasFDerivAt.comp x (g71s_reeb_hasFDerivAt hH hx)
  have hFi := (((g71s_contDiff_F hH.1).differentiable (by simp) x).inv
    (g71s_F_ne hH hx)).hasFDerivAt
  have h2 := hFi.neg.mul ((g71s_hD hH hx).clm_apply (hasFDerivAt_const w x))
  have e : (fun y => ((g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).flip w) (reeb H y)) =
      (fun y => -(fderiv ℝ H y y / 2)⁻¹ * fderiv ℝ H y w) := by
    funext y; simp only [ContinuousLinearMap.flip_apply, g71s_omB_apply, g71s_omega_reeb_left]
  rw [e] at h1
  have := congrArg (fun L => L v) (h1.unique h2)
  simp [hw] at this; rw [this]; ring

lemma g71s_om_R'_right (v w : V n) (hw : fderiv ℝ H x w = 0) :
    omega0 w (fderiv ℝ (reeb H) x v) =
      (fderiv ℝ H x x / 2)⁻¹ * fderiv ℝ (fderiv ℝ H) x v w := by
  rw [g71s_omega_skew, g71s_om_R'_left hH hx v w hw]; ring

/-- the key infinitesimal symplecticity -/
lemma g71s_om_R'_sum (v w : V n) (hv : fderiv ℝ H x v = 0) (hw : fderiv ℝ H x w = 0) :
    omega0 (fderiv ℝ (reeb H) x v) w + omega0 v (fderiv ℝ (reeb H) x w) = 0 := by
  rw [g71s_om_R'_left hH hx v w hw, g71s_om_R'_right hH hx w v hv, g71s_sym hH hx v w]; ring

end geo

lemma g71s_bootstrap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → E}
    {x : ℝ → E} (hx : ∀ τ, HasDerivAt x (g (x τ)) τ) (hg : ∀ τ, ContDiffAt ℝ ∞ g (x τ)) :
    ContDiff ℝ ∞ x := by
  rw [contDiff_infty]; intro m
  induction m with
  | zero => exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun τ => (hx τ).continuousAt)
  | succ m ih =>
    rw [show ((m+1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_deriv]
    refine ⟨fun τ => (hx τ).differentiableAt, by simp, ?_⟩
    have : deriv x = g ∘ x := funext fun τ => (hx τ).deriv
    rw [this, contDiff_iff_contDiffAt]
    intro τ
    exact ((hg τ).of_le (by exact_mod_cast le_top)).comp τ ih.contDiffAt

section orbit
variable {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
include hH

lemma g71s_reeb_cd (τ : ℝ) : ContDiffAt ℝ ∞ (reeb H) (P.x τ) :=
  g71s_reeb_contDiffAt hH.1 (by have := g71s_F_pos hH (P.mem τ); intro h; rw [h] at this; norm_num at this)

lemma g71s_x_cd : ContDiff ℝ ∞ P.x := g71s_bootstrap P.hasDerivAt (g71s_reeb_cd hH P)

omit hH in
lemma g71s_gamma_deriv (t : ℝ) :
    HasDerivAt (fun t => P.x (P.T * t)) (P.T • reeb H (P.x (P.T * t))) t := by
  have := (P.hasDerivAt (P.T * t)).scomp t ((hasDerivAt_id t).const_mul P.T)
  simp only [mul_one, id] at this
  exact this

lemma g71s_Dreeb_cd : ContDiff ℝ ∞ (fun τ => fderiv ℝ (reeb H) (P.x τ)) := by
  rw [contDiff_iff_contDiffAt]; intro τ
  exact ((g71s_reeb_cd hH P τ).fderiv_right (m := ∞) (by simp)).comp τ (g71s_x_cd hH P).contDiffAt

/-- derivative facts for a ξ-loop -/
lemma g71s_xi_deriv_dH (η : ℝ → V n) (hη : IsXiLoop P η) (t : ℝ) :
    fderiv ℝ H (P.x (P.T * t)) (deriv η t) =
      -(P.T * fderiv ℝ (fderiv ℝ H) (P.x (P.T * t)) (reeb H (P.x (P.T * t))) (η t)) := by
  have hηd : HasDerivAt η (deriv η t) t :=
    ((hη.1.differentiable (by simp)) t).hasDerivAt
  have h2 : HasDerivAt (fun t => fderiv ℝ H (P.x (P.T * t)))
      (fderiv ℝ (fderiv ℝ H) (P.x (P.T * t)) (P.T • reeb H (P.x (P.T * t)))) t :=
    (g71s_hD hH (P.mem (P.T * t))).comp_hasDerivAt t (g71s_gamma_deriv P t)
  have h1 : HasDerivAt (fun t => fderiv ℝ H (P.x (P.T * t)) (η t))
      (fderiv ℝ (fderiv ℝ H) (P.x (P.T * t)) (P.T • reeb H (P.x (P.T * t))) (η t) +
        fderiv ℝ H (P.x (P.T * t)) (deriv η t)) t :=
    h2.clm_apply hηd
  have h0 : HasDerivAt (fun t => fderiv ℝ H (P.x (P.T * t)) (η t)) 0 t := by
    have : (fun t => fderiv ℝ H (P.x (P.T * t)) (η t)) = fun _ => 0 := by
      funext s; exact (hη.2.2 s).2
    rw [this]; exact hasDerivAt_const _ _
  have := h1.unique h0
  rw [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul] at this; linarith

lemma g71s_xi_deriv_om (η : ℝ → V n) (hη : IsXiLoop P η) (t : ℝ) :
    omega0 (P.x (P.T * t)) (deriv η t) =
      -(P.T * omega0 (reeb H (P.x (P.T * t))) (η t)) := by
  have hηd : HasDerivAt η (deriv η t) t :=
    ((hη.1.differentiable (by simp)) t).hasDerivAt
  have h1 := (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).hasDerivAt_of_bilinear
    (fun _ => g71s_gamma_deriv P t) (fun _ => hηd)
  have h0 : HasDerivAt (fun t => (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ) (P.x (P.T * t)) (η t)) 0 t := by
    have : (fun t => (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ) (P.x (P.T * t)) (η t)) = fun _ => 0 := by
      funext s; have := (hη.2.2 s).1; simp only [g71s_omB_apply]; unfold liouville at this; linarith
    rw [this]; exact hasDerivAt_const _ _
  have := h1.unique h0
  simp at this; linarith

/-- the vector inside `asympOp` lies in ξ -/
lemma g71s_inner_xi (η : ℝ → V n) (hη : IsXiLoop P η) (t : ℝ) :
    IsInXi H (P.x (P.T * t))
      (-(deriv η t) + P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (η t)) := by
  have hy := P.mem (P.T * t)
  have hxi := hη.2.2 t
  constructor
  · unfold liouville
    have e1 := g71s_xi_deriv_om hH P η hη t
    have e2 := g71s_om_R' hH hy (η t)
    have e3 := g71s_omega_reeb_left H (P.x (P.T * t)) (η t)
    rw [hxi.2, mul_zero] at e3
    rw [g71s_omega_skew (η t), e3] at e2
    rw [e3] at e1
    have : omega0 (P.x (P.T * t)) (-(deriv η t) + P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (η t))
        = -omega0 (P.x (P.T * t)) (deriv η t) +
          P.T * omega0 (P.x (P.T * t)) (fderiv ℝ (reeb H) (P.x (P.T * t)) (η t)) := by
      simp only [← g71s_omB_apply, map_add, map_neg, map_smul, smul_eq_mul]
    rw [this, e1, e2]; simp
  · rw [map_add, map_neg, map_smul, g71s_xi_deriv_dH hH P η hη t, g71s_dH_R' hH hy,
      g71s_sym hH hy]; simp

lemma g71s_asymp_cd (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (η : ℝ → V n) (hη : IsXiLoop P η) : ContDiff ℝ ∞ (asympOp J P η) := by
  have hγ : ContDiff ℝ ∞ (fun t => P.x (P.T * t)) :=
    (g71s_x_cd hH P).comp (contDiff_const.mul contDiff_id)
  have hd : ContDiff ℝ ∞ (deriv η) := (contDiff_infty_iff_deriv.mp hη.1).2
  have hR : ContDiff ℝ ∞ (fun t => fderiv ℝ (reeb H) (P.x (P.T * t))) :=
    (g71s_Dreeb_cd hH P).comp (contDiff_const.mul contDiff_id)
  unfold asympOp
  exact (hJ.1.comp hγ).clm_apply (hd.neg.add ((hR.clm_apply hη.1).const_smul P.T))

lemma g71s_asymp_xiLoop (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (η : ℝ → V n) (hη : IsXiLoop P η) : IsXiLoop P (asympOp J P η) := by
  refine ⟨g71s_asymp_cd hH P J hJ η hη, ?_, ?_⟩
  · intro t
    have hp : P.x (P.T * (t + 1)) = P.x (P.T * t) := by rw [mul_add, mul_one, P.periodic]
    have hd : deriv η (t + 1) = deriv η t := by
      have e : η = fun s => η (s + 1) := funext fun s => (hη.2.1 s).symm
      conv_rhs => rw [e]
      rw [deriv_comp_add_const]
    simp only [asympOp, hp, hη.2.1 t, hd]
  · intro t
    have hi := g71s_inner_xi hH P η hη t
    exact (hJ.2 _ (P.mem _) _ _ hi hi).1

end orbit

open scoped NNReal

noncomputable def g71s_Bop {H : V n → ℝ} (P : ReebOrbit H) (τ : ℝ) :
    (V n →L[ℝ] V n) →L[ℝ] (V n →L[ℝ] V n) :=
  ContinuousLinearMap.compL ℝ (V n) (V n) (V n) (fderiv ℝ (reeb H) (P.x τ))

lemma g71s_Bop_apply {H : V n → ℝ} (P : ReebOrbit H) (τ : ℝ) (Φ : V n →L[ℝ] V n) :
    g71s_Bop P τ Φ = (fderiv ℝ (reeb H) (P.x τ)).comp Φ := by
  simp [g71s_Bop]

section flow
variable {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
include hH

lemma g71s_Bop_cont : Continuous (g71s_Bop P) :=
  (ContinuousLinearMap.compL ℝ (V n) (V n) (V n)).continuous.comp (g71s_Dreeb_cd hH P).continuous

omit hH in
lemma g71s_Bop_per : Function.Periodic (g71s_Bop P) P.T := by
  intro τ; simp only [g71s_Bop, P.periodic]

lemma g71s_Bop_bound : ∃ K : ℝ≥0, ∀ τ, ‖g71s_Bop P τ‖₊ ≤ K := by
  have hc : Continuous (fun τ => ‖fderiv ℝ (reeb H) (P.x τ)‖) :=
    (g71s_Dreeb_cd hH P).continuous.norm
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := P.T)).exists_bound_of_continuousOn
    hc.continuousOn
  have hper : Function.Periodic (fun τ => ‖fderiv ℝ (reeb H) (P.x τ)‖) P.T := by
    intro τ; simp only [P.periodic]
  refine ⟨Real.toNNReal (max C 0), fun τ => ?_⟩
  obtain ⟨y, hy, hyτ⟩ := hper.exists_mem_Ico₀ P.T_pos τ
  have h1 := hC y (Set.Ico_subset_Icc_self hy)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
  have h2 : ‖fderiv ℝ (reeb H) (P.x τ)‖ ≤ max C 0 := by
    rw [hyτ]; exact h1.trans (le_max_left _ _)
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
  refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun Φ => ?_
  rw [g71s_Bop_apply]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

omit hH in
lemma g71s_isLin_iff (Φ : ℝ → V n →L[ℝ] V n) :
    IsLinReebFlow P Φ ↔ Φ 0 = ContinuousLinearMap.id ℝ (V n) ∧
      ∀ τ, HasDerivAt Φ (g71s_Bop P τ (Φ τ)) τ := by
  simp only [IsLinReebFlow, g71s_Bop_apply]

lemma g71s_flow_exists : ∃ Φ : ℝ → V n →L[ℝ] V n, IsLinReebFlow P Φ := by
  obtain ⟨K, hK⟩ := g71s_Bop_bound hH P
  obtain ⟨Φ, h0, hd⟩ := g71s_lode_exists (g71s_Bop P) (g71s_Bop_cont hH P) K hK
    (ContinuousLinearMap.id ℝ (V n))
  exact ⟨Φ, (g71s_isLin_iff P Φ).2 ⟨h0, hd⟩⟩

lemma g71s_flow_unique (Φ Ψ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow P Φ)
    (hΨ : IsLinReebFlow P Ψ) : Φ = Ψ := by
  obtain ⟨K, hK⟩ := g71s_Bop_bound hH P
  rw [g71s_isLin_iff] at hΦ hΨ
  exact g71s_lode_unique _ K hK Φ Ψ hΦ.2 hΨ.2 0 (hΦ.1.trans hΨ.1.symm)

omit hH in
lemma g71s_flow_vec_deriv (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow P Φ) (v : V n) (τ : ℝ) :
    HasDerivAt (fun τ => Φ τ v) (fderiv ℝ (reeb H) (P.x τ) (Φ τ v)) τ := by
  have := (hΦ.2 τ).clm_apply (hasDerivAt_const τ v)
  simpa using this

lemma g71s_flow_dH (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow P Φ) (v : V n)
    (hv : fderiv ℝ H (P.x 0) v = 0) (τ : ℝ) : fderiv ℝ H (P.x τ) (Φ τ v) = 0 := by
  have hd : ∀ τ, HasDerivAt (fun τ => fderiv ℝ H (P.x τ) (Φ τ v)) 0 τ := by
    intro τ
    have h2 := ((g71s_hD hH (P.mem τ)).comp_hasDerivAt τ (P.hasDerivAt τ)).clm_apply
      (g71s_flow_vec_deriv P Φ hΦ v τ)
    refine h2.congr_deriv ?_
    simp only [Function.comp_apply]
    rw [g71s_dH_R' hH (P.mem τ), g71s_sym hH (P.mem τ)]; ring
  have hc := is_const_of_deriv_eq_zero (fun τ => (hd τ).differentiableAt) (fun τ => (hd τ).deriv)
  rw [hc τ 0, hΦ.1]; simpa using hv

lemma g71s_flow_lam (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow P Φ) (v : V n)
    (hv : IsInXi H (P.x 0) v) (τ : ℝ) : omega0 (P.x τ) (Φ τ v) = 0 := by
  have hd : ∀ τ, HasDerivAt (fun τ => (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ) (P.x τ) (Φ τ v)) 0 τ := by
    intro τ
    have h2 := (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).hasDerivAt_of_bilinear
      (fun _ => P.hasDerivAt τ) (fun _ => g71s_flow_vec_deriv P Φ hΦ v τ)
    refine h2.congr_deriv ?_
    simp only [g71s_omB_apply]
    rw [g71s_om_R' hH (P.mem τ), g71s_omega_skew (Φ τ v), g71s_omega_reeb_left,
      g71s_flow_dH hH P Φ hΦ v hv.2 τ]; ring
  have hc := is_const_of_deriv_eq_zero (fun τ => (hd τ).differentiableAt) (fun τ => (hd τ).deriv)
  have := hc τ 0
  simp only [g71s_omB_apply, hΦ.1, ContinuousLinearMap.id_apply] at this
  rw [this]; have := hv.1; unfold liouville at this; linarith

lemma g71s_flow_om (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow P Φ) (v w : V n)
    (hv : fderiv ℝ H (P.x 0) v = 0) (hw : fderiv ℝ H (P.x 0) w = 0) (τ : ℝ) :
    omega0 (Φ τ v) (Φ τ w) = omega0 v w := by
  have hd : ∀ τ, HasDerivAt (fun τ => (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ) (Φ τ v) (Φ τ w)) 0 τ := by
    intro τ
    have h2 := (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).hasDerivAt_of_bilinear
      (fun _ => g71s_flow_vec_deriv P Φ hΦ v τ) (fun _ => g71s_flow_vec_deriv P Φ hΦ w τ)
    refine h2.congr_deriv ?_
    simp only [g71s_omB_apply]
    have := g71s_om_R'_sum hH (P.mem τ) (Φ τ v) (Φ τ w) (g71s_flow_dH hH P Φ hΦ v hv τ)
      (g71s_flow_dH hH P Φ hΦ w hw τ)
    linarith
  have hc := is_const_of_deriv_eq_zero (fun τ => (hd τ).differentiableAt) (fun τ => (hd τ).deriv)
  have := hc τ 0
  simpa [hΦ.1] using this

lemma g71s_flow_shift (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow P Φ) (τ : ℝ) :
    Φ (τ + P.T) = (Φ τ).comp (Φ P.T) := by
  obtain ⟨K, hK⟩ := g71s_Bop_bound hH P
  have hΦ' := (g71s_isLin_iff P Φ).1 hΦ
  have h := g71s_lode_unique (g71s_Bop P) K hK (fun τ => Φ (τ + P.T)) (fun τ => (Φ τ).comp (Φ P.T))
    (fun τ => by
      have := (hΦ'.2 (τ + P.T)).comp_add_const τ P.T
      rwa [g71s_Bop_per P τ] at this)
    (fun τ => by
      have := (hΦ.2 τ).clm_comp (hasDerivAt_const τ (Φ P.T))
      simp only [ContinuousLinearMap.comp_zero, add_zero] at this
      rw [g71s_Bop_apply, ← ContinuousLinearMap.comp_assoc]; exact this)
    0 (by simp [hΦ.1])
  exact congrFun h τ

end flow

section kernel
variable {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
include hH

lemma g71s_A_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ, ‖fderiv ℝ (reeb H) (P.x τ)‖ ≤ C := by
  have hc : Continuous (fun τ => ‖fderiv ℝ (reeb H) (P.x τ)‖) :=
    (g71s_Dreeb_cd hH P).continuous.norm
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := P.T)).exists_bound_of_continuousOn
    hc.continuousOn
  have hper : Function.Periodic (fun τ => ‖fderiv ℝ (reeb H) (P.x τ)‖) P.T := by
    intro τ; simp only [P.periodic]
  refine ⟨max C 0, le_max_right _ _, fun τ => ?_⟩
  obtain ⟨y, hy, hyτ⟩ := hper.exists_mem_Ico₀ P.T_pos τ
  have h1 := hC y (Set.Ico_subset_Icc_self hy)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
  rw [hyτ]; exact h1.trans (le_max_left _ _)

lemma g71s_flow_cd (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow P Φ) : ContDiff ℝ ∞ Φ := by
  rw [contDiff_infty]; intro m
  induction m with
  | zero => exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun τ => (hΦ.2 τ).continuousAt)
  | succ m ih =>
    rw [show ((m+1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_deriv]
    refine ⟨fun τ => (hΦ.2 τ).differentiableAt, by simp, ?_⟩
    have : deriv Φ = fun τ => (fderiv ℝ (reeb H) (P.x τ)).comp (Φ τ) :=
      funext fun τ => (hΦ.2 τ).deriv
    rw [this]
    exact ((g71s_Dreeb_cd hH P).of_le (by exact_mod_cast le_top)).clm_comp ih

/-- the scalar-vector ODE for loops -/
lemma g71s_loop_unique (y z : ℝ → V n)
    (hy : ∀ t, HasDerivAt y (P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (y t)) t)
    (hz : ∀ t, HasDerivAt z (P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (z t)) t)
    (h0 : y 0 = z 0) : y = z := by
  obtain ⟨C, hC0, hC⟩ := g71s_A_bound hH P
  refine g71s_lode_unique (fun t => P.T • fderiv ℝ (reeb H) (P.x (P.T * t)))
    (Real.toNNReal (P.T * C)) ?_ y z hy hz 0 h0
  intro t
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (mul_nonneg P.T_pos.le hC0), norm_smul,
    Real.norm_eq_abs, abs_of_pos P.T_pos]
  exact mul_le_mul_of_nonneg_left (hC _) P.T_pos.le

lemma g71s_flow_loop_deriv (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow P Φ) (v : V n) (t : ℝ) :
    HasDerivAt (fun t => Φ (P.T * t) v)
      (P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (Φ (P.T * t) v)) t := by
  have h1 := (g71s_flow_vec_deriv P Φ hΦ v (P.T * t)).scomp t ((hasDerivAt_id t).const_mul P.T)
  simp only [mul_one] at h1
  exact h1

lemma g71s_asymp_zero_iff (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (η : ℝ → V n) (hη : IsXiLoop P η) (t : ℝ) :
    asympOp J P η t = 0 ↔ deriv η t = P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (η t) := by
  have hb := g71s_inner_xi hH P η hη t
  unfold asympOp
  constructor
  · intro h
    have h2 := (hJ.2 _ (P.mem _) _ _ hb hb).2.1
    rw [h, map_zero] at h2
    have : -deriv η t + P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (η t) = 0 := by
      rw [← neg_eq_zero, ← h2]
    rw [neg_add_eq_zero] at this
    exact this
  · intro h
    rw [h, neg_add_cancel, map_zero]

end kernel

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    (∀ Φ : ℝ → V n →L[ℝ] V n, IsLinReebFlow P Φ → ∀ η : ℝ → V n, IsXiLoop P η →
      ((∀ t : ℝ, asympOp J P η t = 0) ↔ ∀ t : ℝ, η t = Φ (P.T * t) (η 0))) ∧
    (P.IsNondegenerate ↔
      ∀ η : ℝ → V n, IsXiLoop P η → (∀ t : ℝ, asympOp J P η t = 0) → ∀ t : ℝ, η t = 0) := by
  have part1 : ∀ Φ : ℝ → V n →L[ℝ] V n, IsLinReebFlow P Φ → ∀ η : ℝ → V n, IsXiLoop P η →
      ((∀ t : ℝ, asympOp J P η t = 0) ↔ ∀ t : ℝ, η t = Φ (P.T * t) (η 0)) := by
    intro Φ hΦ η hη
    have hηd : ∀ t, HasDerivAt η (deriv η t) t := fun t =>
      ((hη.1.differentiable (by simp)) t).hasDerivAt
    constructor
    · intro h
      have e := g71s_loop_unique hH P η (fun t => Φ (P.T * t) (η 0))
        (fun t => by
          have := hηd t
          rwa [(g71s_asymp_zero_iff hH P J hJ η hη t).1 (h t)] at this)
        (fun t => g71s_flow_loop_deriv hH P Φ hΦ (η 0) t)
        (by simp [hΦ.1])
      exact fun t => congrFun e t
    · intro h t
      have e : η = fun t => Φ (P.T * t) (η 0) := funext h
      rw [g71s_asymp_zero_iff hH P J hJ η hη t]
      have h1 := (g71s_flow_loop_deriv hH P Φ hΦ (η 0) t).deriv
      conv_lhs => rw [e]
      rw [h t]
      exact h1
  refine ⟨part1, ?_⟩
  constructor
  · intro hnd η hη hker t
    obtain ⟨Φ, hΦ⟩ := g71s_flow_exists hH P
    have h1 := (part1 Φ hΦ η hη).1 hker
    have hxi : IsInXi H (P.x 0) (η 0) := by
      have := hη.2.2 0; rwa [mul_zero] at this
    have hfix : Φ P.T (η 0) = η 0 := by
      have := h1 1; rw [mul_one] at this; rw [← this]; exact (by simpa using hη.2.1 0)
    have h0 := hnd Φ hΦ (η 0) hxi hfix
    rw [h1 t, h0, map_zero]
  · intro hker Φ hΦ v hv hfix
    let η : ℝ → V n := fun t => Φ (P.T * t) v
    have hloop : IsXiLoop P η := by
      refine ⟨?_, ?_, ?_⟩
      · exact ((g71s_flow_cd hH P Φ hΦ).comp (contDiff_const.mul contDiff_id)).clm_apply
          contDiff_const
      · intro t
        simp only [η]
        have e : Φ (P.T * (t + 1)) = Φ (P.T * t + P.T) := congrArg Φ (by ring)
        rw [e, g71s_flow_shift hH P Φ hΦ, ContinuousLinearMap.comp_apply, hfix]
      · intro t
        refine ⟨?_, g71s_flow_dH hH P Φ hΦ v hv.2 _⟩
        unfold liouville; rw [g71s_flow_lam hH P Φ hΦ v hv _]; simp
    have hη0 : η 0 = v := by simp [η, hΦ.1]
    have hk := hker η hloop ((part1 Φ hΦ η hloop).2 (fun t => by rw [hη0]))
    rw [← hη0]; exact hk 0
