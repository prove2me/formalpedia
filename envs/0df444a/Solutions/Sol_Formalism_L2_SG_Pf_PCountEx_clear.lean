-- Prove2me | solution 1 for Formalism.L2.SG.Pf.PCountEx.clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:30:32.323234+00:00
-- url     : https://prove2.me/submissions/571e8482-8706-45cf-ab37-68b2c4fe9efc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IotaFIntMem
import Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_iotaF_int_mem
import Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_clear_one
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
namespace Formalism.L2.SG.Pf.PCountEx
section Clear
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
private theorem algebraMap_ιF_mem_O (p : HeightOneSpectrum (𝓞 F)) (t : 𝓞 F) :
    algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have hm := iotaF_int_mem A p t
  have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) =
      algebraMap (𝒪[(A p).Fp]) (A p).Ep ⟨_, hm⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap
end Clear
section Mat
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p) {n : ℕ}
end Mat
end Formalism.L2.SG.Pf.PCountEx
end
end

set_option autoImplicit false
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.PCountEx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
namespace Formalism.L2.SG.Pf.PCountEx
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 F))) {ι : Type} [Fintype ι] (z : ∀ p, ι → (A p).Ep) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ p ∈ S, ∀ k,
      algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * z p k ∈ (A p).O := by
  classical
  choose t ht0 ht using fun q : S × ι => clear_one A q.1.1 (z q.1 q.2)
  refine ⟨∏ q, t q, Finset.prod_ne_zero_iff.2 (fun q _ => ht0 q), fun p hp k => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ (⟨⟨p, hp⟩, k⟩ : S × ι))]
  simp only [map_mul]
  rw [mul_comm (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t ⟨⟨p, hp⟩, k⟩)))), mul_assoc]
  exact Subring.mul_mem _ (algebraMap_ιF_mem_O A p _) (ht ⟨⟨p, hp⟩, k⟩)
end Formalism.L2.SG.Pf.PCountEx
