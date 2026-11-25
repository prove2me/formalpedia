-- Prove2me | solution 1 for Formalism.L2.Col.BiPair.sumOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:38.036067+00:00
-- url     : https://prove2.me/submissions/daf2250b-de02-48c2-a350-32a247d61c12

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_csOf_mem

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
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.BiPair
variable {S S' : GSD K} (P : BiPair S S')
namespace Formalism.L2.Col.BiPair
theorem _root_.solution (h' : S'.Ok) (s' : S'.Sec) (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hB : ∀ d', ∀ x ∈ N (P.p d'), ∀ y ∈ N' d', P.B x y ∈ (1 : Submodule (𝓞 K) K)) (n : ℕ)
    (hn : ∀ c, (S'.toCSDOf h' s').wt c ∣ n) (φ : S.EqFun) (hφ : φ ∈ S.intOf N) (ψ : S'.EqFun)
    (hψ : ψ ∈ S'.intOf N') : (n : 𝓞 K) • P.sumOf h' s' φ ψ ∈ (1 : Submodule (𝓞 K) K) := by
  unfold sumOf
  exact S'.csOf_mem h' s' 1 _ (fun d' => hB d' _ (hφ (P.p d')) _ (hψ d')) n hn
end Formalism.L2.Col.BiPair
