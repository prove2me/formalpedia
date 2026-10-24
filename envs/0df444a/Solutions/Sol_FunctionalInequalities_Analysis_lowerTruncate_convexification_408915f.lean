-- Prove2me | solution 1 for FunctionalInequalities.Analysis.lowerTruncate_convexification_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:25:45.244886+00:00
-- url     : https://prove2.me/submissions/4335febb-cc77-47b1-b855-aa8957f8a984

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_legendre_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_ne_bot_iff_408915f

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The Legendre transform reverses pointwise order, including extended values. -/
theorem FunctionalInequalities.Analysis.legendre_antitone {φ ψ : E → EReal} (h : ∀ x, φ x ≤ ψ x) (y : E) :
    legendre ψ y ≤ legendre φ y := by
  apply iSup_le
  intro x
  exact (EReal.sub_le_sub le_rfl (h x)).trans
    (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
/-- One finite value excludes `-∞` for the entire Legendre transform. -/
theorem FunctionalInequalities.Analysis.legendre_ne_bot (φ : E → EReal) (hφ : ProperPotential φ) (y : E) :
    legendre φ y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hφ.2
  have hb := hφ.1 x
  lift φ x to ℝ using ⟨hx, hb⟩ with r hr
  have hle : ((inner ℝ x y - r : ℝ) : EReal) ≤ legendre φ y := by
    change ((inner ℝ x y - r : ℝ) : EReal) ≤
      ⨆ z : E, (inner ℝ z y : EReal) - φ z
    simpa only [← hr, EReal.coe_sub] using
      (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hle)
/-- Fenchel inequality for a proper extended potential; no convexity is assumed. -/
theorem FunctionalInequalities.Analysis.fenchel_le (φ : E → EReal) (hφ : ProperPotential φ) (x y : E) :
    (inner ℝ x y : EReal) ≤ φ x + legendre φ y := by
  have h := le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x
  have hi := (EReal.sub_le_iff_le_add (.inl (hφ.1 x))
    (.inr (legendre_ne_bot φ hφ y))).mp h
  simpa only [add_comm] using hi
/-- The biconjugate never exceeds a proper extended potential. -/
theorem FunctionalInequalities.Analysis.biconjugate_le (φ : E → EReal) (hφ : ProperPotential φ) (x : E) :
    legendre (legendre φ) x ≤ φ x := by
  apply iSup_le
  intro y
  exact EReal.sub_le_of_le_add (by
    simpa only [real_inner_comm] using fenchel_le φ hφ x y)
/-- A real lower bound on the primal gives a finite upper bound for its
Legendre transform at zero. This is the normalization used after CEK (61). -/
theorem FunctionalInequalities.Analysis.legendre_zero_le_of_lower_bound (φ : E → EReal) (M : ℝ)
    (h : ∀ x, ((-M : ℝ) : EReal) ≤ φ x) : legendre φ 0 ≤ (M : EReal) := by
  apply iSup_le
  intro x
  simp only [inner_zero_right, EReal.coe_zero, zero_sub]
  apply EReal.neg_le.mpr
  simpa only [EReal.coe_neg] using h x
/-- For proper primal and dual potentials, convexification does not alter the
Legendre transform. This is the identity used for `φ_ℓ = (g_ℓ*)*` in Proposition 12. -/
theorem FunctionalInequalities.Analysis.triconjugate_eq (φ : E → EReal) (hφ : ProperPotential φ)
    (hdual : ProperPotential (legendre φ)) (y : E) :
    legendre (legendre (legendre φ)) y = legendre φ y := by
  apply le_antisymm
  · exact biconjugate_le (legendre φ) hdual y
  · exact legendre_antitone (biconjugate_le φ hφ) y
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A single finite-value witness makes the lower truncation proper;
the input need not be convex, nonnegative, or globally finite. -/
theorem FunctionalInequalities.Analysis.lowerTruncate_proper (φ : E → EReal) (M : ℝ)
    (hfinite : ∃ x, φ x ≠ ⊤) : ProperPotential (lowerTruncate φ M) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact ne_of_gt ((EReal.bot_lt_coe (-M)).trans_le (le_max_right _ _))
  · obtain ⟨x, hx⟩ := hfinite
    refine ⟨x, ne_of_lt ?_⟩
    exact max_lt (Ne.lt_top hx) (EReal.coe_lt_top (-M))
/-- Both sides of the truncation/conjugation construction are proper,
so the triple-conjugate identity has hypotheses available from the data. -/
theorem FunctionalInequalities.Analysis.legendre_lowerTruncate_proper (φ : E → EReal) (M : ℝ)
    (hfinite : ∃ x, φ x ≠ ⊤) : ProperPotential (legendre (lowerTruncate φ M)) := by
  refine ⟨legendre_ne_bot _ (lowerTruncate_proper φ M hfinite), 0, ?_⟩
  exact ne_of_lt ((legendre_zero_le_of_lower_bound _ M
    (fun x => le_max_right _ _)).trans_lt (EReal.coe_lt_top M))
/-- Every affine summand of the actual extended-real conjugate is continuous,
including when its fixed intercept is an infinite value. -/
theorem FunctionalInequalities.Analysis.continuous_legendre_summand (φ : E → EReal) (x : E) :
    Continuous (fun y : E => (inner ℝ x y : EReal) - φ x) := by
  by_cases hb : φ x = ⊥
  · simpa only [hb, EReal.coe_sub_bot] using
      (continuous_const : Continuous (fun _ : E => (⊤ : EReal)))
  by_cases ht : φ x = ⊤
  · simpa only [ht, EReal.sub_top] using
      (continuous_const : Continuous (fun _ : E => (⊥ : EReal)))
  lift φ x to ℝ using ⟨ht, hb⟩ with r hr
  have hc : Continuous (fun y : E => inner ℝ x y - r) :=
    (continuous_const.inner continuous_id).sub continuous_const
  simpa only [Function.comp_def, ← hr, ← EReal.coe_sub] using continuous_coe_real_ereal.comp hc
/-- The conjugate is lower semicontinuous for any extended-real input;
no properness, convexity, finite dimension or global finiteness is required. -/
theorem FunctionalInequalities.Analysis.lowerSemicontinuous_legendre (φ : E → EReal) :
    LowerSemicontinuous (legendre φ) := by
  exact lowerSemicontinuous_iSup (fun x =>
    (continuous_legendre_summand φ x).lowerSemicontinuous)
/-- Conjugation produces a convex potential from precisely a nonempty effective
domain, without any convexity or lower-semicontinuity premise on the primal. -/
theorem FunctionalInequalities.Analysis.convexPotential_legendre (φ : E → EReal) (hfinite : ∃ x, φ x ≠ ⊤) :
    ConvexPotential (legendre φ) :=
  ⟨fun y => (legendre_ne_bot_iff_408915f φ y).mpr hfinite, convex_epigraph_legendre_408915f φ⟩
/-- The CEK lower bound persists through biconjugation. -/
theorem FunctionalInequalities.Analysis.lower_bound_biconjugate (φ : E → EReal) (M : ℝ)
    (hlower : ∀ x, ((-M : ℝ) : EReal) ≤ φ x) (x : E) :
    ((-M : ℝ) : EReal) ≤ legendre (legendre φ) x := by
  have hzero := legendre_zero_le_of_lower_bound φ M hlower
  have hneg : ((-M : ℝ) : EReal) ≤ -legendre φ 0 := by
    simpa only [EReal.coe_neg] using (EReal.neg_le_neg_iff.mpr hzero)
  have hterm : -legendre φ 0 ≤ legendre (legendre φ) x := by
    change -legendre φ 0 ≤ ⨆ z : E, (inner ℝ z x : EReal) - legendre φ z
    simpa only [inner_zero_left, EReal.coe_zero, zero_sub] using
      (le_iSup (fun z : E => (inner ℝ z x : EReal) - legendre φ z) 0)
  exact hneg.trans hterm
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- CEK Proposition 12's actual truncation/convexification has a convex lsc proper
output, retains the lower bound and pointwise upper bound, and preserves its
conjugate. Only a finite primal witness is needed; input convexity is unnecessary. -/
theorem solution (φ : E → EReal) (M : ℝ)
    (hfinite : ∃ x, φ x ≠ ⊤) :
    let g := FunctionalInequalities.Analysis.lowerTruncate φ M
    let c := FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.legendre g)
    FunctionalInequalities.Analysis.ConvexPotential c ∧ LowerSemicontinuous c ∧ FunctionalInequalities.Analysis.ProperPotential c ∧
      (∀ x, ((-M : ℝ) : EReal) ≤ c x ∧ c x ≤ g x) ∧
      (∀ y, FunctionalInequalities.Analysis.legendre c y = FunctionalInequalities.Analysis.legendre g y) := by
  dsimp only
  have hg := FunctionalInequalities.Analysis.lowerTruncate_proper φ M hfinite
  have hdual := FunctionalInequalities.Analysis.legendre_lowerTruncate_proper φ M hfinite
  have hc := FunctionalInequalities.Analysis.convexPotential_legendre (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.lowerTruncate φ M)) hdual.2
  refine ⟨hc, FunctionalInequalities.Analysis.lowerSemicontinuous_legendre _, ?_, ?_, FunctionalInequalities.Analysis.triconjugate_eq _ hg hdual⟩
  · obtain ⟨x, hx⟩ := hg.2
    refine ⟨hc.1, x, ne_of_lt ?_⟩
    exact (FunctionalInequalities.Analysis.biconjugate_le _ hg x).trans_lt (Ne.lt_top hx)
  · intro x
    exact ⟨FunctionalInequalities.Analysis.lower_bound_biconjugate _ M (fun y => le_max_right _ _) x,
      FunctionalInequalities.Analysis.biconjugate_le _ hg x⟩
