-- Prove2me | solution 1 for BianchiIX.exists_deep_taub_crossing
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:06:03.853383+00:00
-- url     : https://prove2.me/submissions/db25f0c9-be6c-42ea-9472-1c83c699cba2

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.ByContra
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Lattice

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_last_sublevel_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hb : f b < 0) :
    ∃ c ∈ Ico a b, (c = a ∨ f c = 0) ∧
      (∀ t ∈ Icc c b, f t ≤ 0) ∧ ∀ t ∈ Ioc c b, f t < 0 := by
  let K := Icc a b ∩ f ⁻¹' Ici 0
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici) inter_subset_left
  obtain ⟨c, hc⟩ := (hK.insert a).exists_isGreatest (by simp)
  have hca : a ≤ c := hc.2 (mem_insert a K)
  have hcb : c < b := by
    rcases hc.1 with hca' | hcK
    · simpa only [hca'] using hab
    · exact lt_of_le_of_ne hcK.1.2 (by intro heq; subst c; exact (not_le_of_gt hb) hcK.2)
  have hright : ∀ t ∈ Ioc c b, f t < 0 := by
    intro t ht
    by_contra! hneg
    have htK : t ∈ K := ⟨⟨hca.trans ht.1.le, ht.2⟩, hneg⟩
    exact (not_le_of_gt ht.1) (hc.2 (mem_insert_of_mem a htK))
  have hclosed : IsClosed (Icc a b ∩ f ⁻¹' Iic 0) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hclosure := closure_minimal (fun t (ht : t ∈ Ioc c b) =>
    show t ∈ Icc a b ∩ f ⁻¹' Iic 0 from ⟨⟨hca.trans ht.1.le, ht.2⟩, (hright t ht).le⟩) hclosed
  rw [closure_Ioc hcb.ne] at hclosure
  have hnonpos : ∀ t ∈ Icc c b, f t ≤ 0 := fun t ht => (hclosure ht).2
  refine ⟨c, ⟨hca, hcb⟩, ?_, hnonpos, hright⟩
  rcases hc.1 with hca' | hcK
  · exact Or.inl hca'
  · exact Or.inr (le_antisymm (hnonpos c ⟨le_rfl, hcb.le⟩) hcK.2)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.constraint_small_wall_products {p s n b c Δ : ℝ}
    (hc : constraint p s n b c = 1)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hbc : 4 * b * c ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2)
    (hΔ : 0 ≤ Δ ∧ Δ ≤ 1 / 4) :
    p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 1 + 3 / 2 * Δ ^ 2 ∧
      p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 35 / 32 ∧ |p| < 17 / 16 := by
  have hsum : p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 1 + 3 / 2 * Δ ^ 2 := by
    dsimp [constraint, shearSq, curvature] at hc
    nlinarith only [hc, hnb, hbc, hcn]
  have hΔsq : Δ ^ 2 ≤ 1 / 16 := by nlinarith only [hΔ.1, hΔ.2]
  have hsum' : p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 35 / 32 := by
    linarith only [hsum, hΔsq]
  have hpsq : p ^ 2 < (17 / 16 : ℝ) ^ 2 := by
    nlinarith only [hsum', sq_nonneg s, sq_nonneg n, sq_nonneg b, sq_nonneg c]
  refine ⟨hsum, hsum', abs_lt.mpr ⟨?_, ?_⟩⟩ <;> nlinarith only [hpsq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.taubRadiusSq_nonneg (s b c : ℝ) : 0 ≤ taubRadiusSq s b c :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.taubRadiusHalfRate_identity {p s n b c : ℝ} (hc : constraint p s n b c = 1) :
    (1 - p) * taubRadiusHalfRate p s n b c =
      -p * (b - c) ^ 2 * taubRadiusSq s b c +
        n * ((n - 2 * (b + c)) * ((1 - p) * taubRadiusSq s b c - (b - c) ^ 2) +
          (1 - p) * Real.sqrt 3 * s * (b - c)) := by
  unfold constraint shearSq curvature at hc
  unfold taubRadiusHalfRate taubRadiusSq shearMinus rateTwo rateThree shearSq curvature
  linear_combination p * (b - c) ^ 2 * hc

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.taub_negative_wall_rate {p s : ℝ} (hp : p ≤ -1 / 2) : rateOne p s ≤ -5 / 4 := by
  unfold rateOne shearSq
  nlinarith [sq_nonneg (p + 1 / 2), sq_nonneg s]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.taubRadiusHalfRate_lower {p s n b c : ℝ}
    (hc : constraint p s n b c = 1) (hp : p ≤ -1 / 2) (hn : 0 ≤ n)
    (hwall : n ^ 2 + b ^ 2 + c ^ 2 ≤ 2) :
    -5 * n * taubRadiusSq s b c ≤ taubRadiusHalfRate p s n b c := by
  let R := taubRadiusSq s b c
  let A := (1 - p) * R - (b - c) ^ 2
  have hR : 0 ≤ R := taubRadiusSq_nonneg s b c
  have hvR : (b - c) ^ 2 ≤ R := by dsimp [R, taubRadiusSq]; nlinarith [sq_nonneg s]
  have hP : 0 < 1 - p := by linarith only [hp]
  have hA : 0 ≤ A := by
    have H := mul_nonneg (by linarith only [hp] : 0 ≤ -p) hR
    dsimp [A]
    nlinarith only [hvR, H]
  have hsum : b + c ≤ 2 := by nlinarith [sq_nonneg n, sq_nonneg (b - c), sq_nonneg (b + c - 2)]
  have hq : -4 ≤ n - 2 * (b + c) := by linarith only [hn, hsum]
  have hprod : -4 * (1 - p) * R ≤ (n - 2 * (b + c)) * A := by
    have H := mul_le_mul_of_nonneg_right hq hA
    dsimp [A] at H
    dsimp [A]
    nlinarith only [H, sq_nonneg (b - c)]
  have hcross : -R ≤ Real.sqrt 3 * s * (b - c) := by
    have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have H := sq_nonneg (2 * s + Real.sqrt 3 * (b - c))
    dsimp [R, taubRadiusSq]
    nlinarith [sq_nonneg (b - c)]
  have hcrossP := mul_le_mul_of_nonneg_left hcross hP.le
  have hterms : -5 * (1 - p) * R ≤
      (n - 2 * (b + c)) * A + (1 - p) * Real.sqrt 3 * s * (b - c) := by
    nlinarith only [hprod, hcrossP]
  have htermsN := mul_le_mul_of_nonneg_left hterms hn
  have hgood := mul_nonneg (mul_nonneg (by linarith only [hp] : 0 ≤ -p) (sq_nonneg (b - c))) hR
  have Hid := taubRadiusHalfRate_identity hc
  change (1 - p) * taubRadiusHalfRate p s n b c =
    -p * (b - c) ^ 2 * R + n * ((n - 2 * (b + c)) * A + (1 - p) * Real.sqrt 3 * s * (b - c)) at Hid
  apply (mul_le_mul_iff_right₀ hP).mp
  change (1 - p) * (-5 * n * R) ≤ (1 - p) * taubRadiusHalfRate p s n b c
  nlinarith only [Hid, htermsN, hgood]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_normalizedTaubRadiusSq {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) :
    HasDerivAt (fun u => normalizedTaubRadiusSq (α u))
      (2 * taubRadiusHalfRate (α t 0) (α t 1) (α t 2) (α t 3) (α t 4)) t := by
  obtain ⟨_, hs, _, hb, hc⟩ := hasDerivAt_normalized_components hα
  convert! (hs.pow 2).add ((hb.sub hc).pow 2) using 1
  unfold taubRadiusHalfRate
  simp only [Pi.sub_apply]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_weightedTaubRadiusSq {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) :
    HasDerivAt (fun u => weightedTaubRadiusSq (α u))
      ((2 * taubRadiusHalfRate (α t 0) (α t 1) (α t 2) (α t 3) (α t 4) -
        8 * normalizedTaubRadiusSq (α t) * rateOne (α t 0) (α t 1) * α t 2) * Real.exp (-8 * α t 2)) t := by
  have hn := (hasDerivAt_normalized_components hα).2.2.1
  convert! (hasDerivAt_normalizedTaubRadiusSq hα).mul ((hn.const_mul (-8)).exp) using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.weightedTaubRadiusSq_monotone {α : ℝ → NormalizedState} {a b : ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc a b, stateConstraint (α t) = 1)
    (hp : ∀ t ∈ Icc a b, α t 0 ≤ -1 / 2)
    (hn : ∀ t ∈ Icc a b, 0 ≤ α t 2)
    (hw : ∀ t ∈ Icc a b, (α t 2) ^ 2 + (α t 3) ^ 2 + (α t 4) ^ 2 ≤ 2) :
    MonotoneOn (fun t => weightedTaubRadiusSq (α t)) (Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (HasDerivAt.continuousOn fun t ht => hasDerivAt_weightedTaubRadiusSq (hα t ht))
    (fun t ht => (hasDerivAt_weightedTaubRadiusSq (hα t (interior_subset ht))).hasDerivWithinAt)
  intro t ht
  have ht' := interior_subset ht
  have hr := taubRadiusHalfRate_lower (hc t ht') (hp t ht') (hn t ht') (hw t ht')
  have hnR := mul_nonneg (hn t ht') (taubRadiusSq_nonneg (α t 1) (α t 3) (α t 4))
  have hrate := mul_le_mul_of_nonneg_right (taub_negative_wall_rate (s := α t 1) (hp t ht')) hnR
  apply mul_nonneg _ (Real.exp_pos _).le
  change 0 ≤ 2 * taubRadiusHalfRate _ _ _ _ _ - 8 * taubRadiusSq _ _ _ * rateOne _ _ * α t 2
  nlinarith only [hr, hrate]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.taubRadiusSq_backward_bound {α : ℝ → NormalizedState} {a b h : ℝ}
    (hab : a ≤ b) (hh : h ≤ 1 / 16)
    (hmono : MonotoneOn (fun t => weightedTaubRadiusSq (α t)) (Icc a b))
    (hna : α a 2 ≤ h) (hnb : 0 ≤ α b 2) :
    normalizedTaubRadiusSq (α a) ≤ 2 * normalizedTaubRadiusSq (α b) := by
  have H := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hn : -8 * α b 2 - (-8 * α a 2) ≤ 1 / 2 := by linarith only [hna, hnb, hh]
  have hexp : Real.exp (-8 * α b 2 - (-8 * α a 2)) ≤ 2 := by
    calc
      _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hn
      _ ≤ 2 := by
        convert Real.exp_bound_div_one_sub_of_interval (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) using 1
        norm_num
  have H' := (le_div_iff₀ (Real.exp_pos (-8 * α a 2))).mpr H
  change normalizedTaubRadiusSq (α a) ≤ normalizedTaubRadiusSq (α b) * Real.exp (-8 * α b 2) /
    Real.exp (-8 * α a 2) at H'
  rw [mul_div_assoc, ← Real.exp_sub] at H'
  exact H'.trans (by
    have := mul_le_mul_of_nonneg_left hexp (taubRadiusSq_nonneg (α b 1) (α b 3) (α b 4))
    simpa only [normalizedTaubRadiusSq, mul_comm] using this)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedEuclideanDistance_nonneg (x y : NormalizedState) :
    0 ≤ normalizedEuclideanDistance x y := dist_nonneg

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedEuclideanDistance_sq (x y : NormalizedState) :
    normalizedEuclideanDistance x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  simp [normalizedEuclideanDistance, EuclideanSpace.dist_sq_eq, Real.dist_eq]

end
end

private theorem BianchiIX.normalizedTaubDistance_sq (x : NormalizedState) :
    normalizedEuclideanDistance x (taubPoint 0) ^ 2 =
      (1 + x 0) ^ 2 + normalizedTaubRadiusSq x + x 2 ^ 2 + 2 * x 3 * x 4 := by
  rw [normalizedEuclideanDistance_sq]
  simp [taubPoint, Fin.sum_univ_succ, normalizedTaubRadiusSq, taubRadiusSq]
  ring


/-- A deep Taub visit is preceded by a transverse crossing of the fixed small main-wall section. -/
theorem solution {α : ℝ → NormalizedState} {a b h d ε : ℝ}
    (hab : a < b) (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    (hε : 0 < ε) (hεd : ε < d / 4)
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc a b, stateConstraint (α t) = 1)
    (hp : ∀ t ∈ Icc a b, positiveWalls (α t))
    (hprod : ∀ t ∈ Icc a b, normalizedWallProductsBound (d / 4) (α t))
    (ha : 4 * ε ^ 2 < normalizedTaubRadiusSq (α a))
    (hb : normalizedEuclideanDistance (α b) (taubPoint 0) ≤ ε) :
    ∃ c ∈ Ioo a b, α c 2 = h ∧ α c 0 < -1 / 2 ∧ |α c 1| < d ∧
      α c 3 < d ∧ α c 4 < d ∧
      normalizedTaubRadiusSq (α c) ≤ 2 * normalizedTaubRadiusSq (α b) ∧
      normalizedField (α c) 2 ≤ -5 * h / 4 := by
  have hbmem : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hεh : ε < h := by linarith only [hεd, hdh, hd, hh]
  have hεsmall : ε < 1 / 16 := hεh.trans_le hhmax
  have hdist : normalizedEuclideanDistance (α b) (taubPoint 0) ^ 2 ≤ ε ^ 2 :=
    pow_le_pow_left₀ (normalizedEuclideanDistance_nonneg _ _) hb 2
  rw [normalizedTaubDistance_sq] at hdist
  have hR0 : 0 ≤ normalizedTaubRadiusSq (α b) := taubRadiusSq_nonneg _ _ _
  have hbc : 0 ≤ α b 3 * α b 4 := mul_nonneg (hp b hbmem).2.1.le (hp b hbmem).2.2.le
  have hRb : normalizedTaubRadiusSq (α b) ≤ ε ^ 2 := by
    nlinarith only [hdist, hbc, sq_nonneg (1 + α b 0), sq_nonneg (α b 2)]
  have hpb : α b 0 < -1 / 2 := by
    nlinarith [sq_nonneg (α b 0 + 1 - ε), sq_nonneg (α b 2)]
  have hnb : α b 2 < h := by
    have hn := (hp b hbmem).1
    nlinarith [sq_nonneg (1 + α b 0)]
  let f := fun t => max (α t 0 + 1 / 2) (α t 2 - h)
  have hf : ContinuousOn f (Icc a b) := by
    have hpcont := HasDerivAt.continuousOn fun t ht => (hasDerivAt_normalized_components (hα t ht)).1
    have hncont := HasDerivAt.continuousOn fun t ht => (hasDerivAt_normalized_components (hα t ht)).2.2.1
    exact (hpcont.add continuousOn_const).sup (hncont.sub continuousOn_const)
  obtain ⟨c, hcab, hboundary, hclosed, _⟩ := exists_last_sublevel_interval hab hf
    (max_lt (by linarith only [hpb]) (by linarith only [hnb]))
  have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc hcab.1 le_rfl
  have hbounds (t : ℝ) (ht : t ∈ Icc c b) : α t 0 ≤ -1 / 2 ∧ α t 2 ≤ h := by
    have H := max_le_iff.mp (hclosed t ht)
    constructor <;> linarith only [H.1, H.2]
  have hwall (t : ℝ) (ht : t ∈ Icc a b) :
      (α t 2) ^ 2 + (α t 3) ^ 2 + (α t 4) ^ 2 ≤ 2 := by
    have H := (constraint_small_wall_products (hc t ht) (hprod t ht).1
      (hprod t ht).2.1 (hprod t ht).2.2
      ⟨by positivity, by linarith only [hdh, hhmax]⟩).2.1
    nlinarith only [H, sq_nonneg (α t 0), sq_nonneg (α t 1)]
  have hmono := weightedTaubRadiusSq_monotone (fun t ht => hα t (hsub ht))
    (fun t ht => hc t (hsub ht)) (fun t ht => (hbounds t ht).1)
    (fun t ht => (hp t (hsub ht)).1.le) (fun t ht => hwall t (hsub ht))
  have hcc : c ∈ Icc c b := ⟨le_rfl, hcab.2.le⟩
  have hcfull : c ∈ Icc a b := hsub hcc
  have hRc := taubRadiusSq_backward_bound hcab.2.le hhmax hmono (hbounds c hcc).2 (hp b hbmem).1.le
  have hRε : normalizedTaubRadiusSq (α c) ≤ 2 * ε ^ 2 := hRc.trans (by linarith only [hRb])
  have hca : a < c := by
    apply lt_of_le_of_ne hcab.1
    intro heq
    subst c
    nlinarith only [ha, hRε, sq_nonneg ε]
  have hpc : α c 0 < -1 / 2 := by
    have Hc := hc c hcfull
    have Hn := (hp c hcfull).1.le
    have Hbc := mul_nonneg Hn (add_nonneg (hp c hcfull).2.1.le (hp c hcfull).2.2.le)
    have Hrad : (α c 0) ^ 2 + normalizedTaubRadiusSq (α c) + (α c 2) ^ 2 -
        2 * α c 2 * (α c 3 + α c 4) = 1 := by
      dsimp [stateConstraint, constraint, shearSq, curvature] at Hc
      dsimp [normalizedTaubRadiusSq, taubRadiusSq]
      nlinarith only [Hc]
    have Hn2 := pow_le_pow_left₀ Hn ((hbounds c hcc).2.trans hhmax) 2
    have Hε2 := pow_le_pow_left₀ hε.le hεsmall.le 2
    have Hple := (hbounds c hcc).1
    apply lt_of_le_of_ne Hple
    intro heq
    rw [heq] at Hrad
    nlinarith only [Hrad, Hbc, Hn2, Hε2, hRε]
  have hnc : α c 2 = h := by
    have heq : f c = 0 := hboundary.resolve_left (ne_of_gt hca)
    apply le_antisymm (hbounds c hcc).2
    by_contra! hlt
    have H : f c < 0 := max_lt (by linarith only [hpc]) (by linarith only [hlt])
    rw [heq] at H
    exact (lt_irrefl 0) H
  have hs : |α c 1| < d := by
    have H := sq_nonneg (α c 3 - α c 4)
    dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hRε
    rw [abs_lt]
    constructor <;> nlinarith
  have hsum : α c 3 + α c 4 < d := by
    have H := (hprod c hcfull).2.1
    have Hr : (α c 3 - α c 4) ^ 2 ≤ 2 * ε ^ 2 := by
      dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hRε
      nlinarith only [hRε, sq_nonneg (α c 1)]
    nlinarith only [H, Hr, hεd, hε, hd, sq_nonneg (d - 4 * ε)]
  refine ⟨c, ⟨hca, hcab.2⟩, hnc, hpc, hs, ?_, ?_, hRc, ?_⟩
  · linarith only [hsum, (hp c hcfull).2.2]
  · linarith only [hsum, (hp c hcfull).2.1]
  · change rateOne (α c 0) (α c 1) * α c 2 ≤ _
    rw [hnc]
    have H := mul_le_mul_of_nonneg_right (taub_negative_wall_rate (s := α c 1) hpc.le) hh.le
    linarith only [H]
