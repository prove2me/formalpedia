-- Prove2me | solution 1 for CubicNewton.StarConvex.run_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:21:22.727873+00:00
-- url     : https://prove2.me/submissions/448e3998-fcf8-42d6-af66-cc513cb37e7d

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_StarConvex_IsStarConvexFn

open scoped RealInnerProductSpace

namespace CubicNewton.StarConvex

lemma cn_abs_le_of_deriv (u u' : ℝ → ℝ) (C : ℝ) (p : ℕ)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u (u' t) t)
    (hb : ∀ t ∈ Set.Icc (0:ℝ) 1, |u' t| ≤ C * t ^ p) (h0 : u 0 = 0) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, |u t| ≤ C * t ^ (p+1) / (p+1) := by
  intro t ht
  have hcont : ContinuousOn u (Set.Icc 0 1) := fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hpoly : ∀ s : ℝ, HasDerivAt (fun s:ℝ => C * s^(p+1)/(p+1)) (C * s^p) s := by
    intro s
    have := ((hasDerivAt_pow (p+1) s).const_mul C).div_const ((p:ℝ)+1)
    refine this.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  have hpc : ContinuousOn (fun s:ℝ => C * s^(p+1)/(p+1)) (Set.Icc 0 1) :=
    fun s _ => (hpoly s).continuousAt.continuousWithinAt
  have hint : interior (Set.Icc (0:ℝ) 1) = Set.Ioo 0 1 := interior_Icc
  have m1 : MonotoneOn (fun s => C * s^(p+1)/(p+1) - u s) (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) (f' := fun s => C * s^p - u' s)
      (hpc.sub hcont)
    · intro s hs; rw [hint] at hs
      exact ((hpoly s).sub (hu s (Set.Ioo_subset_Icc_self hs))).hasDerivWithinAt
    · intro s hs; rw [hint] at hs
      have := hb s (Set.Ioo_subset_Icc_self hs); have := le_abs_self (u' s)
      linarith
  have m2 : MonotoneOn (fun s => C * s^(p+1)/(p+1) + u s) (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) (f' := fun s => C * s^p + u' s)
      (hpc.add hcont)
    · intro s hs; rw [hint] at hs
      exact ((hpoly s).add (hu s (Set.Ioo_subset_Icc_self hs))).hasDerivWithinAt
    · intro s hs; rw [hint] at hs
      have := hb s (Set.Ioo_subset_Icc_self hs); have := neg_abs_le (u' s)
      linarith
  have a := m1 (Set.left_mem_Icc.2 zero_le_one) ht ht.1
  have b := m2 (Set.left_mem_Icc.2 zero_le_one) ht ht.1
  simp only [h0] at a b
  have e : C * (0:ℝ) ^ (p+1) / (p+1) = 0 := by simp
  rw [e] at a b
  rw [abs_le]; constructor <;> linarith

theorem taylor_core {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖) :
    ∀ x ∈ F, ∀ y ∈ F,
      |f y - f x - ⟪g x, y - x⟫ - (1 / 2) * ⟪H x (y - x), y - x⟫| ≤ L / 6 * ‖y - x‖ ^ 3 := by
  intro x hx y hy
  set d := y - x with hd
  let γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x + t • d
  have hγF : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ F := fun t ht => hF_convex.add_smul_sub_mem hx hy ht
  have hγ : ∀ t : ℝ, HasDerivAt γ d t := by
    intro t
    exact (((hasDerivAt_id t).smul_const d).const_add x).congr_deriv (by simp)
  have hgγ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun t => g (γ t)) (H (γ t) d) t :=
    fun t ht => (hg (γ t) (hγF t ht)).comp_hasDerivAt t (hγ t)
  let ψ : ℝ → ℝ := fun t => ⟪g (γ t), d⟫ - ⟪g x, d⟫ - t * ⟪H x d, d⟫
  let ψ' : ℝ → ℝ := fun t => ⟪H (γ t) d, d⟫ - ⟪H x d, d⟫
  have hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (ψ' t) t := by
    intro t ht
    have h1 := (hgγ t ht).inner ℝ (hasDerivAt_const t d)
    have h2 := (hasDerivAt_id t).mul_const (⟪H x d, d⟫)
    exact ((h1.sub_const (⟪g x, d⟫)).sub h2).congr_deriv (by simp [ψ'])
  have hψb : ∀ t ∈ Set.Icc (0:ℝ) 1, |ψ' t| ≤ (L * ‖d‖ ^ 3) * t ^ 1 := by
    intro t ht
    have e : ψ' t = ⟪(H (γ t) - H x) d, d⟫ := by
      simp [ψ', inner_sub_left]
    rw [e]
    have hn : ‖γ t - x‖ = t * ‖d‖ := by
      simp [γ, norm_smul, abs_of_nonneg ht.1]
    have hL := hLip (γ t) (hγF t ht) x hx
    rw [hn] at hL
    calc |⟪(H (γ t) - H x) d, d⟫| ≤ ‖(H (γ t) - H x) d‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖H (γ t) - H x‖ * ‖d‖) * ‖d‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (L * (t * ‖d‖) * ‖d‖) * ‖d‖ := by gcongr
      _ = (L * ‖d‖ ^ 3) * t ^ 1 := by ring
  have hψ0 : ψ 0 = 0 := by simp [ψ, γ]
  have Bψ := cn_abs_le_of_deriv ψ ψ' _ 1 hψ hψb hψ0
  let φ : ℝ → ℝ := fun t => f (γ t) - f x - t * ⟪g x, d⟫ - t ^ 2 / 2 * ⟪H x d, d⟫
  have hφ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt φ (ψ t) t := by
    intro t ht
    have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hf (γ t) (hγF t ht))).comp_hasDerivAt t (hγ t)
    have h2 := (hasDerivAt_id t).mul_const (⟪g x, d⟫)
    have h3 := ((hasDerivAt_pow 2 t).div_const 2).mul_const (⟪H x d, d⟫)
    refine (((h1.sub_const (f x)).sub h2).sub h3).congr_deriv ?_
    simp [ψ, InnerProductSpace.toDual_apply_apply]
  have hφb : ∀ t ∈ Set.Icc (0:ℝ) 1, |ψ t| ≤ (L * ‖d‖ ^ 3 / 2) * t ^ 2 := by
    intro t ht
    have := Bψ t ht
    calc |ψ t| ≤ L * ‖d‖ ^ 3 * t ^ (1 + 1) / (1 + 1) := by exact_mod_cast this
      _ = _ := by ring
  have hφ0 : φ 0 = 0 := by simp [φ, γ]
  have Bφ := cn_abs_le_of_deriv φ ψ _ 2 hφ hφb hφ0 1 (Set.right_mem_Icc.2 zero_le_one)
  have e1 : φ 1 = f y - f x - ⟪g x, y - x⟫ - (1 / 2) * ⟪H x (y - x), y - x⟫ := by
    simp [φ, γ, hd]
  rw [← e1]
  calc |φ 1| ≤ L * ‖d‖ ^ 3 / 2 * 1 ^ (2 + 1) / (2 + 1) := by exact_mod_cast Bφ
    _ = L / 6 * ‖y - x‖ ^ 3 := by rw [hd]; ring

theorem model_core {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L M : ℝ) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ∀ y ∈ F, f x + CubicNewton.Shared.cubicModel g H M x T ≤ f y + (L + M) / 6 * ‖y - x‖ ^ 3 := by
  intro y hy
  have h1 := hT y
  have h2 := taylor_core F f g H L hF_convex hf hg hLip x hx y hy
  have h3 := neg_abs_le (f y - f x - ⟪g x, y - x⟫ - (1 / 2) * ⟪H x (y - x), y - x⟫)
  unfold CubicNewton.Shared.cubicModel at h1 ⊢
  linarith

theorem monotone_core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L₀ L : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    ∀ k, f (x (k + 1)) ≤ f (x k) := by
  intro k
  have h1 := hrun.step k (x k)
  have h2 := hrun.accept k
  have h0 : CubicNewton.Shared.cubicModel g H (M k) (x k) (x k) = 0 := by
    simp [CubicNewton.Shared.cubicModel]
  linarith

/-- one step inequality: for any α ∈ [0,1], δ_{k+1} ≤ (1-α) δ_k + L/2 α³ D³ -/
theorem step_core {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L L₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hF_convex : Convex ℝ F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hstar : IsStarConvexFn F f) (hF_bdd : Bornology.IsBounded F)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ)
    (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : ∀ y, f xs ≤ f y) (k : ℕ) (α : ℝ)
    (hα : α ∈ Set.Icc (0:ℝ) 1) :
    f (x (k+1)) - f xs ≤ (1 - α) * (f (x k) - f xs) + L / 2 * α ^ 3 * Metric.diam F ^ 3 := by
  have hmono : ∀ j, f (x j) ≤ f x₀ := by
    intro j; induction j with
    | zero => rw [hrun.init]
    | succ j ih => exact (monotone_core f g H L₀ L x₀ x M hrun j).trans ih
  have hxk : x k ∈ F := interior_subset (hlevel (hmono k))
  have hxsF : xs ∈ F := interior_subset (hlevel (hxs x₀))
  set y := α • xs + (1 - α) • x k with hy
  have hyF : y ∈ F := by
    have := hF_convex.add_smul_sub_mem hxk hxsF hα
    convert this using 1
    rw [hy, smul_sub, sub_smul, one_smul]; abel
  have hstep := hrun.step k
  have hmodel := model_core F f g H L (M k) hF_convex hf hg hLip (x k) (x (k+1)) hxk hstep y hyF
  have hacc := hrun.accept k
  have hsc := hstar.2 xs hxs (x k) hxk α hα
  have hMk := hrun.param_mem k
  have hnorm : ‖y - x k‖ = α * ‖xs - x k‖ := by
    have : y - x k = α • (xs - x k) := by
      rw [hy, smul_sub, sub_smul, one_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα.1]
  have hD : ‖xs - x k‖ ≤ Metric.diam F := by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hF_bdd hxsF hxk
  have hn0 : 0 ≤ ‖xs - x k‖ := norm_nonneg _
  have hcube : ‖y - x k‖ ^ 3 ≤ α ^ 3 * Metric.diam F ^ 3 := by
    rw [hnorm, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0 hD 3) (pow_nonneg hα.1 3)
  have hLM : (L + M k) / 6 ≤ L / 2 := by linarith [hMk.2]
  have hc0 : 0 ≤ ‖y - x k‖ ^ 3 := pow_nonneg (norm_nonneg _) 3
  have hq : (L + M k) / 6 * ‖y - x k‖ ^ 3 ≤ L / 2 * (α ^ 3 * Metric.diam F ^ 3) := by
    calc (L + M k) / 6 * ‖y - x k‖ ^ 3 ≤ L / 2 * ‖y - x k‖ ^ 3 :=
          mul_le_mul_of_nonneg_right hLM hc0
      _ ≤ L / 2 * (α ^ 3 * Metric.diam F ^ 3) :=
          mul_le_mul_of_nonneg_left hcube (by linarith)
  nlinarith

end CubicNewton.StarConvex

open CubicNewton.StarConvex


theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L₀ L : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    ∀ k, f (x (k + 1)) ≤ f (x k) := by
  exact monotone_core f g H L₀ L x₀ x M hrun
