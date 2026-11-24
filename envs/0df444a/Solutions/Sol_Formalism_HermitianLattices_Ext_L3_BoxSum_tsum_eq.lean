-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.tsum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:29.537782+00:00
-- url     : https://prove2.me/submissions/48561153-625a-4ba2-94af-050a2fa31124

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_mem_idealLattice_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_gW_smul
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_finite_boxSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_mem_boxSet_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_rEmb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter Topology MeasureTheory Pointwise
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) {N : ℝ} (hN : 0 < N) :
    ∑' x : ↑(sBox F ∩ N⁻¹ • (mixedEmbedding.idealLattice F (fracU hI) : Set (mixedEmbedding.mixedSpace F))), gW F m x =
      (∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1)) * N⁻¹ ^ (Formalism.HermitianLatticesTheory.fDeg K * (m - 1)) := by
  have hfin : {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I}.Finite :=
    (finite_boxSet hK hF N).subset fun n hn => hn.1
  have hmem : ∀ n : {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I}, N⁻¹ • mixedEmbedding F ((n : 𝓞 F) : F) ∈
      sBox F ∩ N⁻¹ • (mixedEmbedding.idealLattice F (fracU hI) : Set (mixedEmbedding.mixedSpace F)) := by
    rintro ⟨n, hn, hnI⟩
    refine ⟨fun w => ?_, Set.smul_mem_smul_set ((mem_idealLattice_iff hI _).2 ⟨n, hnI, rfl⟩)⟩
    have h1 := (mem_boxSet_iff hK hF).1 hn w
    rw [Prod.smul_fst, Pi.smul_apply, mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul,
      ← rEmb_apply]
    refine ⟨mul_pos (inv_pos.2 hN) h1.1, ?_⟩
    rw [inv_mul_le_iff₀ hN, mul_one]
    exact h1.2
  let ε : {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I} →
      ↑(sBox F ∩ N⁻¹ • (mixedEmbedding.idealLattice F (fracU hI) : Set (mixedEmbedding.mixedSpace F))) := fun n => ⟨_, hmem n⟩
  have hε : Function.Bijective ε := by
    constructor
    · intro n n' h
      have h1 : N⁻¹ • mixedEmbedding F ((n : 𝓞 F) : F) = N⁻¹ • mixedEmbedding F ((n' : 𝓞 F) : F) :=
        congrArg Subtype.val h
      have h2 := smul_right_injective _ (inv_ne_zero hN.ne') h1
      exact Subtype.ext (RingOfIntegers.coe_injective (mixedEmbedding_injective F h2))
    · rintro ⟨x, hx, hxL⟩
      obtain ⟨y, hy, rfl⟩ := hxL
      obtain ⟨n, hnI, rfl⟩ := (mem_idealLattice_iff hI _).1 hy
      refine ⟨⟨n, (mem_boxSet_iff hK hF).2 fun w => ?_, hnI⟩, rfl⟩
      have h1 := hx w
      simp only [] at h1
      rw [Prod.smul_fst, Pi.smul_apply, mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul,
        ← rEmb_apply, inv_mul_le_iff₀ hN, mul_one] at h1
      exact ⟨(mul_pos_iff_of_pos_left (inv_pos.2 hN)).1 h1.1, h1.2⟩
  have : Finite {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I} := hfin
  rw [← (Equiv.ofBijective ε hε).tsum_eq, tsum_eq_finsum (Set.toFinite _), finsum_mem_mul,
    ← finsum_set_coe_eq_finsum_mem]
  refine finsum_congr fun n => ?_
  exact gW_smul hK hF m n.2.1 _
end Formalism.HermitianLattices.Ext.L3.BoxSum
