-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.int_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:16.817798+00:00
-- url     : https://prove2.me/submissions/67d193e8-f6b6-4dc5-9e22-0e5d15df2242

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_L2_NT_IsTeich_injective

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    (κ : 𝓞 I.E ⧸ w.asIdeal) : ∃ c : ℤ, (c : 𝓞 I.E ⧸ w.asIdeal) = κ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := charP_residue_of_card_eq_prime I w hp hcard
  haveI : Finite (𝓞 I.E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 I.E ⧸ w.asIdeal)
  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) (𝓞 I.E ⧸ w.asIdeal)) :=
    (ZMod.castHom (dvd_refl p) (𝓞 I.E ⧸ w.asIdeal)).injective
  have hbij := (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard]⟩
  obtain ⟨x, hx⟩ := hbij.2 κ
  refine ⟨(x.val : ℤ), ?_⟩
  rw [← hx, ZMod.castHom_apply, Int.cast_natCast, ZMod.natCast_val]
end Formalism.L2.SG.Pf.RedBasicsPf
