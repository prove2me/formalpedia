-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.conv_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:10.56752+00:00
-- url     : https://prove2.me/submissions/54a421f2-3fb6-47c9-a088-bae0d1bdcd2c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.CSym
namespace Formalism.InvariantFactorPaths.G7.CSym
theorem _root_.solution {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] (f g : ℕ → K) (E : ℕ → V)
    (i : ℕ) :
    ∑ l ∈ range (i + 1), f l • ∑ l' ∈ range (i - l + 1), g l' • E (i - l - l') =
      ∑ n ∈ range (i + 1), (∑ a ∈ range (n + 1), f a * g (n - a)) • E (i - n) := by
  simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
  have hin : ∀ l ∈ range (i + 1), ∑ l' ∈ range (i - l + 1), (f l * g l') • E (i - l - l') =
      ∑ n ∈ Ico l (i + 1), (f l * g (n - l)) • E (i - n) := by
    intro l hl
    simp only [Finset.mem_range] at hl
    rw [Finset.sum_Ico_eq_sum_range, show i + 1 - l = i - l + 1 by omega]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [show l + l' - l = l' by omega, show i - (l + l') = i - l - l' by omega]
  rw [Finset.sum_congr rfl hin]
  exact Finset.sum_comm' (fun l n => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)
end Formalism.InvariantFactorPaths.G7.CSym
