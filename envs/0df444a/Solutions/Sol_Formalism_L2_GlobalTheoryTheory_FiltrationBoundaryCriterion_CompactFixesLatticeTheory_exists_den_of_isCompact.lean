-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:24:45.319892+00:00
-- url     : https://prove2.me/submissions/cd2ab38b-1531-45ba-9fa9-4bb8fa672b43

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_MemClosureOfMemSS
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_Imports
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompact
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_algebraMap_mem_intAd
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_continuous_coord
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_exists_sub_mem_intAd
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_isOpen_intAd
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_mem_SS_of_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
private theorem exists_basis_mem_intOE :
    ∃ n : ℕ, ∃ b : Module.Basis (Fin n) F E, ∀ i, b i ∈ intOE E := by
  classical
  let c := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
  have hyF : IsUnit ((y : ℤ) : F) := (Int.cast_ne_zero.mpr hy0).isUnit
  refine ⟨_, c.isUnitSMul (w := fun _ => ((y : ℤ) : F)) (fun _ => hyF), fun i => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul F]
  exact ⟨⟨_, (mem_integralClosure_iff ℤ E).mpr (hy _ (Finset.mem_image_of_mem c (Finset.mem_univ i)))⟩, rfl⟩
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
end
end

set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
theorem _root_.solution :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ C : Set (AE F E), IsCompact C → ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x ∈ C, (d : F) • x ∈ SS F E := by
  classical
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  intro C hC
  obtain ⟨n, b, hb⟩ := exists_basis_mem_intOE (F := F) (E := E)
  have hsm : ∀ (r : 𝓞 F) (a : AF F), a ∈ intAd F → algebraMap (𝓞 F) F r • a ∈ intAd F := by
    intro r a ha
    rw [Algebra.smul_def]
    exact mul_mem (algebraMap_mem_intAd r) ha
  have pt : ∀ a : AF F, ∃ d : 𝓞 F, d ≠ 0 ∧ algebraMap (𝓞 F) F d • a ∈ intAd F := by
    intro a
    obtain ⟨u, hu⟩ := exists_sub_mem_intAd (F := F) a
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({u} : Finset F)
    have hyu : IsIntegral ℤ ((y : F) * u) := by
      have h := hy u (Finset.mem_singleton_self u)
      rw [zsmul_eq_mul] at h
      exact h
    let m : 𝓞 F := ⟨(y : F) * u, (mem_integralClosure_iff ℤ F).mpr hyu⟩
    have hm : algebraMap (𝓞 F) F m = (y : F) * u := rfl
    refine ⟨(y : 𝓞 F), fun h => hy0 ?_, ?_⟩
    · have h' := congrArg (algebraMap (𝓞 F) F) h
      rw [map_intCast, map_zero] at h'
      exact_mod_cast h'
    · have e : algebraMap (𝓞 F) F (y : 𝓞 F) • a
          = algebraMap F (AF F) (algebraMap (𝓞 F) F (y : 𝓞 F)) * (a - algebraMap F (AF F) u)
            + algebraMap F (AF F) (algebraMap (𝓞 F) F m) := by
        rw [hm, map_intCast, Algebra.smul_def, map_mul]
        ring
      rw [e]
      exact add_mem (mul_mem (algebraMap_mem_intAd _) hu) (algebraMap_mem_intAd m)
  have den : ∀ K : Set (AF F), IsCompact K →
      ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ K, algebraMap (𝓞 F) F d • a ∈ intAd F := by
    intro K hK
    choose dp hdp0 hdp using pt
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover
      (fun a : AF F => (fun z => z - a) ⁻¹' (intAd F : Set (AF F)))
      (fun a => (isOpen_intAd (F := F)).preimage (continuous_id.sub continuous_const))
      (fun z _ => Set.mem_iUnion.mpr ⟨z, by
        show z - z ∈ intAd F
        rw [sub_self]
        exact zero_mem _⟩)
    refine ⟨∏ c ∈ t, dp c, Finset.prod_ne_zero_iff.mpr fun c _ => hdp0 c, fun z hz => ?_⟩
    have hz' := ht hz
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at hz'
    obtain ⟨c, hct, hzc⟩ := hz'
    rw [← Finset.mul_prod_erase t dp hct]
    have e : algebraMap (𝓞 F) F (dp c * ∏ c' ∈ t.erase c, dp c') • z
        = algebraMap (𝓞 F) F (dp c * ∏ c' ∈ t.erase c, dp c') • (z - c)
          + algebraMap (𝓞 F) F (∏ c' ∈ t.erase c, dp c') • (algebraMap (𝓞 F) F (dp c) • c) := by
      rw [map_mul, mul_comm]
      simp only [smul_sub, mul_smul]
      abel
    rw [e]
    exact add_mem (hsm _ _ hzc) (hsm _ _ (hdp c))
  have hK : ∀ i, IsCompact (coord b i '' C) := fun i => hC.image (continuous_coord b i)
  choose d hd0 hd using fun i => den _ (hK i)
  refine ⟨∏ i, d i, Finset.prod_ne_zero_iff.mpr fun i _ => hd0 i, fun x hx => ?_⟩
  refine mem_SS_of_coord b hb _ fun i => ?_
  rw [map_smul, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
  show algebraMap (𝓞 F) F (d i * ∏ j ∈ Finset.univ.erase i, d j) • coord b i x ∈ intAd F
  rw [map_mul, mul_comm, mul_smul]
  exact hsm _ _ (hd i _ ⟨x, hx, rfl⟩)
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
