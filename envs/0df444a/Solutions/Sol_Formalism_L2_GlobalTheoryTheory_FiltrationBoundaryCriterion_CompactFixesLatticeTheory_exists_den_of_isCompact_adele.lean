-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_isCompact_adele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:30.613132+00:00
-- url     : https://prove2.me/submissions/a89aa14e-142d-4ad0-9db2-eb8fe58a10e2

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_CompactFixesLattice
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_isOpen_intAd
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_smul_mem_intAd
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_exists_den_adele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
theorem _root_.solution (C : Set (AF F)) (hC : IsCompact C) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ C, (d : F) • a ∈ intAd F := by
  classical
  have hopen : ∀ d : {d : 𝓞 F // d ≠ 0},
      IsOpen {a : AF F | ((d : 𝓞 F) : F) • a ∈ intAd F} := by
    intro d
    have hc : Continuous fun a : AF F => algebraMap F (AF F) ((d : 𝓞 F) : F) * a :=
      continuous_const.mul continuous_id
    have := isOpen_intAd.preimage hc
    convert this using 1
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, Algebra.smul_def]
  have hcov : C ⊆ ⋃ d : {d : 𝓞 F // d ≠ 0}, {a : AF F | ((d : 𝓞 F) : F) • a ∈ intAd F} := by
    intro a _
    obtain ⟨d, hd, h⟩ := exists_den_adele a
    exact Set.mem_iUnion.mpr ⟨⟨d, hd⟩, h⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover _ hopen hcov
  refine ⟨∏ d ∈ t, (d : 𝓞 F), Finset.prod_ne_zero_iff.mpr fun d _ => d.2, fun a ha => ?_⟩
  obtain ⟨d, hdt, hd⟩ := Set.mem_iUnion₂.mp (ht ha)
  have hd' : ((d : 𝓞 F) : F) • a ∈ intAd F := hd
  rw [← Finset.mul_prod_erase t _ hdt, mul_comm]
  have e : (((∏ x ∈ t.erase d, (x : 𝓞 F)) * (d : 𝓞 F) : 𝓞 F) : F) =
      ((∏ x ∈ t.erase d, (x : 𝓞 F) : 𝓞 F) : F) * ((d : 𝓞 F) : F) := rfl
  rw [e, mul_smul]
  exact smul_mem_intAd _ hd'
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
