-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.ms_mu_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:41:39.406896+00:00
-- url     : https://prove2.me/submissions/100eb3ae-de6f-4758-b0c3-9fa96f48f24c

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_ms_rkK_pos
import Theorems.Thm_Formalism_BranchingDeterminantCap_ms_nPl_pos
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_size_maximal_slope


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hfg : L.FG) (hL : L ≠ ⊥) :
    muDef b X L = -(Real.log (ht b X L) / ((nPl K : ℝ) * (rkK L : ℝ))) := by
  have h := size_maximal_slope K V ι b X hX L hfg hL
  obtain ⟨-, h2, -⟩ := h
  obtain ⟨-, -, hpos⟩ := place_lattice_structure K V ι b X hX L hfg
  have hf : (0 : ℝ) < nPl K := by exact_mod_cast ms_nPl_pos
  have hj : (0 : ℝ) < rkK L := by exact_mod_cast ms_rkK_pos b hL
  rw [h2]
  unfold size
  rw [Real.log_rpow hpos]
  field_simp
end Formalism.BranchingDeterminantCap
