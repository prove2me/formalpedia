-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmA_odd_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:09.741624+00:00
-- url     : https://prove2.me/submissions/821ff8c3-f59c-4085-9537-96733e944272

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l : ℕ) (hl : 2 ≤ l) :
    HasSum (fun e : ℕ => if Odd e then ((l : ℝ) ^ e)⁻¹ else 0) (gam l) := by
  have hl0 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  set r : ℝ := ((l : ℝ) ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hl0 (by norm_num))
  have hg : HasSum (fun k : ℕ => (l : ℝ)⁻¹ * r ^ k) ((l : ℝ)⁻¹ * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left _
  have hval : (l : ℝ)⁻¹ * (1 - r)⁻¹ = gam l := by
    rw [gam, hr]
    have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h2 : (l : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hval] at hg
  have hodd : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by simpa using h
  rw [← hodd.hasSum_iff]
  · convert hg using 1
    funext k
    have ho : Odd (2 * k + 1) := odd_two_mul_add_one k
    simp only [Function.comp, ho, if_true, hr]
    rw [pow_succ, pow_mul, mul_inv, mul_comm, inv_pow]
  · intro x hx
    rw [if_neg]
    rintro ⟨k, rfl⟩
    exact hx ⟨k, rfl⟩
end Formalism.DworkPowerSeriesWeights
