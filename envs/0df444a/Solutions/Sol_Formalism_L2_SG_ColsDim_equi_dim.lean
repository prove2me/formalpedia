-- Prove2me | solution 1 for Formalism.L2.SG.ColsDim.equi_dim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:22.566855+00:00
-- url     : https://prove2.me/submissions/7fca10f9-74a5-48f1-a9ac-bd41195ce21e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Module IsDedekindDomain
namespace Formalism.L2.SG.ColsDim
open Formalism.UG
section Abstract
variable {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf]
end Abstract
section Unitary
open NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
end Unitary
section Proofs
variable {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf)
variable {k : Type} [Field k] {W : Type} [AddCommGroup W] [Module k W]
private theorem exists_doubleCoset_section {Γ' Gf' : Type} [Group Γ'] [Group Gf'] (ιf' : Γ' →* Gf')
    (K' : Subgroup Gf') :
    ∃ s : Classes ιf' K' → Gf', ∀ c, DoubleCoset.mk ιf'.range K' (s c) = c :=
  ⟨fun c => Quotient.out c, fun c => Quotient.out_eq' c⟩
variable {V : Type} [AddCommGroup V] [Module k V]
end Proofs
section SharpProof
open InnerProductSpace
variable {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
end SharpProof
end Formalism.L2.SG.ColsDim
end
end

set_option autoImplicit false
noncomputable section
open Module IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.ColsDim
open Formalism.UG
variable {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf)
variable {k : Type} [Field k] {W : Type} [AddCommGroup W] [Module k W]
namespace Formalism.L2.SG.ColsDim
theorem _root_.solution (hst : StabTriv ιf K) [Finite (Classes ιf K)] [FiniteDimensional k W]
    (ρ : Representation k Γ W) (χ : K →* kˣ) :
    FiniteDimensional k (Equi k ιf K ρ χ) ∧
      finrank k (Equi k ιf K ρ χ) = finrank k W * Nat.card (Classes ιf K) := by
  obtain ⟨s, hs⟩ := exists_doubleCoset_section ιf K
  haveI := Fintype.ofFinite (Classes ιf K)
  let e := decEquiv ιf K hst s hs ρ χ
  haveI : FiniteDimensional k (Equi k ιf K ρ χ) := LinearEquiv.finiteDimensional e.symm
  refine ⟨inferInstance, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card, mul_comm]
end Formalism.L2.SG.ColsDim
