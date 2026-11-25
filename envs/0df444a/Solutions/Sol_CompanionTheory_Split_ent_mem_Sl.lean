-- Prove2me | solution 1 for CompanionTheory.Split.ent_mem_Sl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:14:34.837492+00:00
-- url     : https://prove2.me/submissions/e03fcec8-00e4-4632-843d-7500b624057d

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Theorems.Thm_CompanionTheory_Split_exists_prime
import Theorems.Thm_CompanionTheory_Split_pow_mul_mem
import Theorems.Thm_CompanionTheory_Split_ALint_le_Sl
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct Formalism.UG Formalism.L2
noncomputable section
open CompanionTheory CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L
variable (s : SplitPlace L)
namespace CompanionTheory.Split
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hs : ¬ s.Above l) {x : GA L n} (hx : TrivOutside {s.v} x) (i j : Fin n) :
    ent x i j ∈ Sl L hl := by
  obtain ⟨p, hp, hA, -⟩ := exists_prime s
  obtain ⟨a, ha⟩ := pow_mul_mem s hA fun w => sub_one_supp hx i j
  have h1 : ent x i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ Sl L hl :=
    ⟨p ^ a, fun e => hs (((Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow e)).symm ▸ hA), ha⟩
  have := add_mem h1 (ALint_le_Sl hl ((Umax L n).one_mem i j))
  rwa [show ((1 : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) = 1 from rfl, sub_add_cancel] at this
end CompanionTheory.Split
