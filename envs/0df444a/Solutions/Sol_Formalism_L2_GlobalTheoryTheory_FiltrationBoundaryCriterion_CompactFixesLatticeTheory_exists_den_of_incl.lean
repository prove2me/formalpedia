-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:20:30.315939+00:00
-- url     : https://prove2.me/submissions/4fe0a22d-9550-4aa9-81dd-fa8726926ced

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_MemClosureOfMemSS
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_Imports
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompact
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_coord_mem_of_mem_SS
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_coord_tmul
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_mem_range_of_mem_intAd

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
private theorem exists_int_ne_zero_mul_repr_mem_range {n : ℕ} (b : Module.Basis (Fin n) F E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ e ∈ intOE E, ∀ i, (y : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range := by
  classical
  let g := NumberField.RingOfIntegers.basis E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin n =>
      b.repr (algebraMap (𝓞 E) E (g p.1)) p.2))
  refine ⟨y, hy0, ?_⟩
  rintro _ ⟨z, rfl⟩ i
  have hz : algebraMap (𝓞 E) E z = ∑ j, g.repr z j • algebraMap (𝓞 E) E (g j) := by
    conv_lhs => rw [← g.sum_repr z]
    simp only [map_sum, map_zsmul]
  have key : (y : F) * b.repr (algebraMap (𝓞 E) E z) i
      = ∑ j, g.repr z j • ((y : F) * b.repr (algebraMap (𝓞 E) E (g j)) i) := by
    rw [hz, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, mul_smul_comm]
  rw [key]
  refine sum_mem fun j _ => zsmul_mem ?_ _
  have h2 : IsIntegral ℤ ((y : F) * b.repr (algebraMap (𝓞 E) E (g j)) i) := by
    have h := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, i)))
    rw [zsmul_eq_mul] at h
    exact h
  exact ⟨⟨_, (mem_integralClosure_iff ℤ F).mpr h2⟩, rfl⟩
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
end
end

set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] :
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ e : E, inclE (F := F) (AF F) e ∈ SS F E → (D : F) • e ∈ intOE E := by
  obtain ⟨n, b, hb⟩ := exists_basis_mem_intOE (F := F) (E := E)
  obtain ⟨y, hy0, hy⟩ := exists_int_ne_zero_mul_repr_mem_range b
  have hyF : ((y : 𝓞 F) : F) = (y : F) := by
    rw [show ((y : 𝓞 F) : F) = algebraMap (𝓞 F) F (y : 𝓞 F) from rfl, map_intCast]
  refine ⟨(y : 𝓞 F), fun h => hy0 ?_, fun e he => ?_⟩
  · have h' := congrArg (algebraMap (𝓞 F) F) h
    rw [map_intCast, map_zero] at h'
    exact_mod_cast h'
  have hc : ∀ i, (y : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range := by
    intro i
    have h := coord_mem_of_mem_SS b (y : 𝓞 F) (by rw [hyF]; exact hy) he i
    rw [hyF, show inclE (F := F) (AF F) e = e ⊗ₜ[F] (1 : AF F) from rfl, coord_tmul,
      smul_smul, ← Algebra.algebraMap_eq_smul_one] at h
    exact mem_range_of_mem_intAd _ h
  rw [hyF, ← b.sum_repr e, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  rw [smul_smul]
  obtain ⟨r, hr⟩ := hc i
  rw [← hr, Algebra.smul_def]
  refine mul_mem ?_ (hb i)
  exact ⟨⟨_, (mem_integralClosure_iff ℤ E).mpr ((r.isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F E))⟩, rfl⟩
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
