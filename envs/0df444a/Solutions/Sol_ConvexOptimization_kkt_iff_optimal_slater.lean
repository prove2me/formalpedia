-- Prove2me | solution 1 for ConvexOptimization.kkt_iff_optimal_slater
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-14T13:45:21.721374+00:00
-- url     : https://prove2.me/submissions/7e0c5ef3-63d1-4ff4-bd80-c8310679e362

import Theorems.Thm_ConvexOptimization_slater_strong_duality
import Theorems.Thm_ConvexOptimization_lagrangian_saddle_iff_strong_duality
import Theorems.Thm_ConvexOptimization_complementary_slackness
import Theorems.Thm_ConvexOptimization_kkt_sufficient_for_convex

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open ConvexOptimization

private theorem lagrangian_minimum_stationarity {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (f₀' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf₀' : ∀ x, HasGradientAt f₀ (f₀' x) x)
    (fc' : Fin mm → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hfc' : ∀ i x, HasGradientAt (fc i) (fc' i x) x)
    (xs : EuclideanSpace ℝ (Fin n)) (lam : Fin mm → ℝ) (nu : Fin p → ℝ)
    (hmin : ∀ x, lagrangian f₀ fc a b xs lam nu ≤
      lagrangian f₀ fc a b x lam nu) :
    f₀' xs + ∑ i, lam i • fc' i xs + ∑ j, nu j • a j = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  have hfcSum :
      HasFDerivAt (fun x : E => ∑ i, lam i * fc i x)
        (∑ i, lam i • InnerProductSpace.toDual ℝ E (fc' i xs)) xs := by
    simpa only [Finset.sum_apply] using
      (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
        (hfc' i xs).hasFDerivAt.const_mul (lam i))
  have ha (j : Fin p) :
      HasFDerivAt (fun x : E => ⟪a j, x⟫ - b j)
        (InnerProductSpace.toDual ℝ E (a j)) xs := by
    have hinner : HasFDerivAt (fun x : E => ⟪a j, x⟫)
        (InnerProductSpace.toDual ℝ E (a j)) xs := by
      exact (InnerProductSpace.toDual ℝ E (a j)).hasFDerivAt
    simpa only [Pi.sub_def, sub_zero] using
      hinner.sub (hasFDerivAt_const (𝕜 := ℝ) (E := E) (b j) xs)
  have haSum :
      HasFDerivAt (fun x : E => ∑ j, nu j * (⟪a j, x⟫ - b j))
        (∑ j, nu j • InnerProductSpace.toDual ℝ E (a j)) xs := by
    simpa only [Finset.sum_apply] using
      (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ =>
        (ha j).const_mul (nu j))
  have hL :
      HasFDerivAt (fun x : E => lagrangian f₀ fc a b x lam nu)
        (InnerProductSpace.toDual ℝ E (f₀' xs) +
          ∑ i, lam i • InnerProductSpace.toDual ℝ E (fc' i xs) +
          ∑ j, nu j • InnerProductSpace.toDual ℝ E (a j)) xs := by
    simpa only [lagrangian, Pi.add_def] using
      ((hf₀' xs).hasFDerivAt.add hfcSum).add haSum
  have hglobal : IsMinOn (fun x : E => lagrangian f₀ fc a b x lam nu) Set.univ xs :=
    fun x _ => hmin x
  have hzero := (hglobal.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero hL
  apply (InnerProductSpace.toDual ℝ E).injective
  simpa using hzero

theorem solution {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a)
    (b : Fin p → ℝ)
    (f₀' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf₀' : ∀ x, HasGradientAt f₀ (f₀' x) x)
    (fc' : Fin mm → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hfc' : ∀ i x, HasGradientAt (fc i) (fc' i x) x)
    (xsl : EuclideanSpace ℝ (Fin n)) (hxsl_ineq : ∀ i, fc i xsl < 0)
    (hxsl_eq : ∀ j, ⟪a j, xsl⟫ = b j)
    (xs : EuclideanSpace ℝ (Fin n)) :
    (xs ∈ feasibleSet fc a b ∧ IsMinOn f₀ (feasibleSet fc a b) xs) ↔
      ∃ (lam : Fin mm → ℝ) (nu : Fin p → ℝ),
        IsKKTPoint fc a b f₀' fc' xs lam nu := by
  constructor
  · rintro ⟨hfeas, hmin⟩
    have hxmem : f₀ xs ∈ f₀ '' feasibleSet fc a b := ⟨xs, hfeas, rfl⟩
    have himage : (f₀ '' feasibleSet fc a b).Nonempty := ⟨f₀ xs, hxmem⟩
    have hbdd : BddBelow (f₀ '' feasibleSet fc a b) := by
      refine ⟨f₀ xs, ?_⟩
      rintro z ⟨y, hy, rfl⟩
      exact hmin hy
    have hsinf : sInf (f₀ '' feasibleSet fc a b) = f₀ xs := by
      apply le_antisymm
      · exact csInf_le hbdd hxmem
      · apply le_csInf himage
        rintro z ⟨y, hy, rfl⟩
        exact hmin hy
    obtain ⟨lam, nu, hlam, hdual⟩ :=
      slater_strong_duality f₀ hf₀ fc hfc a ha b xsl hxsl_ineq hxsl_eq hbdd
    have hzero : dualFunction f₀ fc a b lam nu = (f₀ xs : EReal) :=
      hdual.trans (congrArg (fun r : ℝ => (r : EReal)) hsinf)
    have hcomp : ∀ i, lam i * fc i xs = 0 :=
      complementary_slackness f₀ fc a b xs hfeas lam hlam nu hzero
    have hLmin : ∀ x, lagrangian f₀ fc a b xs lam nu ≤
        lagrangian f₀ fc a b x lam nu :=
      ((lagrangian_saddle_iff_strong_duality f₀ fc a b xs lam hlam nu).2
        ⟨hfeas, hmin, hzero⟩).2
    have hstat : f₀' xs + ∑ i, lam i • fc' i xs + ∑ j, nu j • a j = 0 :=
      lagrangian_minimum_stationarity f₀ fc a b f₀' hf₀' fc' hfc' xs lam nu hLmin
    refine ⟨lam, nu, ?_⟩
    exact ⟨hfeas.1, hfeas.2, hlam, hcomp, hstat⟩
  · rintro ⟨lam, nu, hkkt⟩
    exact kkt_sufficient_for_convex f₀ hf₀ fc hfc a b f₀' hf₀' fc' hfc'
      xs lam nu hkkt
