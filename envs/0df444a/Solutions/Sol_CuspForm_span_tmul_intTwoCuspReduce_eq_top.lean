-- Prove2me | solution 1 for CuspForm.span_tmul_intTwoCuspReduce_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/12ff9629-dedd-5ace-a453-0f089f7d4c04

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_span_tmul_intTwoCuspReduce_eq_top

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

namespace CuspForm
p2m_export "CuspForm" "mk ext IntTwoCuspForms intTwoCuspReduce intTwoCuspReduce_surjective twoCuspIntegralSet twoCuspLattice twoCuspIntegralSet_subset_twoCuspLattice"
namespace Eng1bP2
p2m_open "CuspForm"

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem span_intTwoCuspReduce_eq_top :
    Submodule.span (ZMod p) {y : CuspForm.IntTwoCuspForms M H p |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)),
          y = CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩} = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := CuspForm.intTwoCuspReduce_surjective M H p x
  have htop : (Submodule.span (⊥ : Subring ℂ)
      (((↑) : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) → CuspForm (CohCarrier.GammaH M H) 2) ⁻¹'
        CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
      Submodule (⊥ : Subring ℂ) ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ))) = ⊤ :=
    Submodule.span_span_coe_preimage
  have hy : y ∈ Submodule.span (⊥ : Subring ℂ)
      (((↑) : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) → CuspForm (CohCarrier.GammaH M H) 2) ⁻¹'
        CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) := by
    rw [htop]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
      obtain ⟨n, hn⟩ := Subring.mem_bot.mp a.2
      have ha : a = (n : (⊥ : Subring ℂ)) := Subtype.ext (by exact hn.symm)
      rw [ha, Int.cast_smul_eq_zsmul, map_zsmul]
      exact zsmul_mem hy n

end CuspForm.Eng1bP2

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (K : Type*) [Field K] [Algebra (ZMod p) K] :
    Submodule.span K {x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)),
          x = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩} = ⊤ := by
  have hset : {x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)),
          x = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩} =
      TensorProduct.mk (ZMod p) K (CuspForm.IntTwoCuspForms M H p) 1 ''
        {y : CuspForm.IntTwoCuspForms M H p |
          ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)),
            y = CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩} := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
  rw [hset, ← Submodule.baseChange_span, CuspForm.Eng1bP2.span_intTwoCuspReduce_eq_top,
    Submodule.baseChange_top]

end S_CuspForm_span_tmul_intTwoCuspReduce_eq_top
end P2MW
export P2MW.S_CuspForm_span_tmul_intTwoCuspReduce_eq_top (solution)
