-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.int_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:31:07.455416+00:00
-- url     : https://prove2.me/submissions/75418554-f8f4-4779-b2eb-68e9b015655b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise
namespace Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))
private lemma charP_residue_of_card_eq_prime {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) :
    CharP (𝓞 I.E ⧸ w.asIdeal) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (𝓞 I.E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 I.E ⧸ w.asIdeal)
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hcard])
end Formalism.L2.SG.Pf.RedBasicsPf
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedBasicsPf
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (c : ℤ) :
    (c : 𝓞 I.E) ∈ w.asIdeal ↔ (p : ℤ) ∣ c := by
  haveI := charP_residue_of_card_eq_prime I w hp hcard
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast, CharP.intCast_eq_zero_iff _ p]
end Formalism.L2.SG.Pf.RedBasicsPf
