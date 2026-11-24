-- Prove2me | solution 1 for Formalism.HN.frameB_share
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:25.337745+00:00
-- url     : https://prove2.me/submissions/acbe8370-870c-4716-b1b0-3fda3584c283

import Definitions.Def_Formalism_HarderNarasimhan_StatementFrame
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNExtreme
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_LayerCakeFormula
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset Formalism.CorankShareLayerCake.FR
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {I : Type} [Fintype I] (m : I → ℕ) (x : ∀ i, Fin (m i) → ℝ) (s u τ : ℝ)
    (hu : 0 < u) (hτ : 0 ≤ τ) (hsum : (∑ i, (m i : ℝ)) * s ≤ ∑ i, ∑ j, x i j)
    (hle : ∀ i j, x i j ≤ s + u) :
    (∑ i, ((univ.filter (fun j => x i j < s - τ)).card : ℝ)) ≤ (∑ i, (m i : ℝ)) * (u / (u + τ)) := by
  have hone : ∀ i, ∑ j, x i j ≤ ((univ.filter (fun j => x i j < s - τ)).card : ℝ) * (s - τ) +
      ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) * (s + u) := by
    intro i
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => x i j < s - τ)]
    have hc := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (m i))))
      (fun j => x i j < s - τ)
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have hc' : ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) =
        ((univ.filter (fun j => ¬ x i j < s - τ)).card : ℝ) := by
      have hc2 : ((univ.filter (fun j => x i j < s - τ)).card : ℝ) +
          ((univ.filter (fun j => ¬ x i j < s - τ)).card : ℝ) = (m i : ℝ) := by exact_mod_cast hc
      linarith
    rw [hc']
    have h1 : ∑ j ∈ univ.filter (fun j => x i j < s - τ), x i j ≤
        ∑ _j ∈ univ.filter (fun j => x i j < s - τ), (s - τ) :=
      Finset.sum_le_sum fun j hj => (Finset.mem_filter.1 hj).2.le
    have h2 : ∑ j ∈ univ.filter (fun j => ¬ x i j < s - τ), x i j ≤
        ∑ _j ∈ univ.filter (fun j => ¬ x i j < s - τ), (s + u) :=
      Finset.sum_le_sum fun j _ => hle i j
    rw [Finset.sum_const, nsmul_eq_mul] at h1 h2
    linarith
  have htot := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset I)) => hone i
  have hexp : ∑ i, (((univ.filter (fun j => x i j < s - τ)).card : ℝ) * (s - τ) +
      ((m i : ℝ) - (univ.filter (fun j => x i j < s - τ)).card) * (s + u)) =
      (∑ i, (m i : ℝ)) * (s + u) - (∑ i, ((univ.filter (fun j => x i j < s - τ)).card : ℝ)) * (u + τ) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexp] at htot
  have hut : 0 < u + τ := by linarith
  rw [mul_div_assoc', le_div_iff₀ hut]
  nlinarith
end Formalism.HN
