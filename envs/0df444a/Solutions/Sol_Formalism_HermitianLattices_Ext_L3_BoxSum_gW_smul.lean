-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.gW_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:42.188853+00:00
-- url     : https://prove2.me/submissions/dc44c90c-d5da-4527-aec1-bea0a0fc63ad

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_absNorm_eq_prod_of_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_card_real
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_rEmb_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology MeasureTheory Pointwise
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) (c : ℝ) :
    gW F m (c • mixedEmbedding F (n : F)) =
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * c ^ (Formalism.HermitianLatticesTheory.fDeg K * (m - 1)) := by
  unfold gW
  rw [absNorm_eq_prod_of_mem hK hF hn, ← Finset.prod_pow, pow_mul, ← card_real hK hF,
    ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Prod.smul_fst, Pi.smul_apply, mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul, mul_pow,
    rEmb_apply, mul_comm]
end Formalism.HermitianLattices.Ext.L3.BoxSum
