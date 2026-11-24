-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.relIndex_scaled_span_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:44.328201+00:00
-- url     : https://prove2.me/submissions/768bb8f0-368d-42a4-9e72-8466d776067b

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HN_DualPolygon_twist_finrank_int
import Theorems.Thm_Formalism_HN_DualPolygon_twist_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {K ι : Type} [Field K] [NumberField K] [Fintype ι]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution {j : ℕ} (e : Fin j → ι → K) (he : LinearIndependent K e) (m : ℕ) (hm : m ≠ 0) :
    (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex
        (Submodule.span (𝓞 K) (Set.range fun a => (m : K)⁻¹ • e a)).toAddSubgroup =
      m ^ (finrank ℚ K * j) := by
  classical
  let _ : StarRing K := starRingOfComm
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm
  set e' : Fin j → ι → K := fun a => (m : K)⁻¹ • e a with he'
  have hli : LinearIndependent K e' :=
    he.units_smul (fun _ => (Units.mk0 (m : K) hmK)⁻¹)
  set X := Submodule.span (𝓞 K) (Set.range e') with hX
  have hfg : X.FG := Submodule.fg_span (Set.finite_range e')
  have h1 : (Ideal.span {(m : 𝓞 K)}) • X = Submodule.span (𝓞 K) (Set.range e) := by
    rw [Submodule.ideal_span_singleton_smul, hX, Submodule.smul_span]
    congr 1
    ext x
    simp only [Set.mem_smul_set, Set.mem_range, exists_exists_eq_and]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨a, ?_⟩
      rw [he', ← algebraMap_smul K (m : 𝓞 K), smul_smul]
      simp [hmK]
    · rintro ⟨a, rfl⟩
      refine ⟨a, ?_⟩
      rw [he', ← algebraMap_smul K (m : 𝓞 K), smul_smul]
      simp [hmK]
  have h2 := Formalism.HN.DualPolygon.twist_int X hfg m hm
  rw [h1, Formalism.HN.DualPolygon.twist_finrank_int X hfg] at h2
  rw [h2, hX, Submodule.span_span_of_tower, finrank_span_eq_card hli, Fintype.card_fin]
end Formalism.HermiteSiegelSlopes
