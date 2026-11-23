-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.isMackey_pi_upper_unipotent_prod_character
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:52.835012+00:00
-- url     : https://prove2.me/submissions/6f015c90-cbc4-41d2-99f7-7df8c6712aef

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnLocal
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_mackey_product
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_mirabolic_is_mackey


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (K : Type) [Field K] [NumberField K]
    (ι : Type) [Fintype ι] [DecidableEq ι] (k : ι → Type) [∀ v, Field (k v)] [∀ v, Finite (k v)] (n : ℕ)
    (χ : ∀ v, AddChar (k v) (𝓞 K)) (hχ : ∀ v, χ v ≠ 1)
    (P : ∀ v, Subgroup (GL (Fin (n + 1)) (k v))) (U : ∀ v, Subgroup (P v))
    (hP : ∀ v, ∀ h : GL (Fin (n + 1)) (k v), h ∈ P v ↔ IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) (k v)))
    (hU : ∀ v, ∀ h : P v, h ∈ U v ↔
      IsUniU ((h : GL (Fin (n + 1)) (k v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (k v))) :
    IsMackey (Subgroup.pi Set.univ U) (fun h : (∀ v, P v) =>
      ∏ v, χ v (supd (((h v : P v) : GL (Fin (n + 1)) (k v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (k v)))) := mackey_product ι (𝓞 K) (fun v => ↥(P v)) U
    (fun v (h : P v) => χ v (supd (((h : GL (Fin (n + 1)) (k v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (k v)))))
    (fun v => mirabolic_is_mackey (k v) (𝓞 K) n (χ v) (hχ v) (P v) (U v) (hP v) (hU v))
end Formalism.EigenvalueLevelCeiling
