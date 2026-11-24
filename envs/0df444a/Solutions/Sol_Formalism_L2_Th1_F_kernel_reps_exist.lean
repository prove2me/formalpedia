-- Prove2me | solution 1 for Formalism.L2.Th1.F.kernel_reps_exist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:53:00.77453+00:00
-- url     : https://prove2.me/submissions/c1ec0336-c251-486b-a763-a7a48ccfbfb4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Theorems.Thm_Formalism_L2_Th1_F_Ker_card_quot
import Theorems.Thm_Formalism_L2_Th1_F_Ker_mk_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Ker
namespace Formalism.L2.Th1.F
theorem _root_.solution : KerRepsExist := by
  unfold KerRepsExist
  intro L α hα h
  haveI : Finite (L.lattice ⧸ LinearMap.range (mulEnd L α h)) := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    have hc := card_quot L α hα h
    rw [h0] at hc
    have hn : Complex.normSq α = 0 := by rw [← hc]; simp
    exact hα (Complex.normSq_eq_zero.1 hn)
  have hout : ∀ q : L.lattice ⧸ LinearMap.range (mulEnd L α h), Submodule.Quotient.mk (Quotient.out q) = q :=
    fun q => Quotient.out_eq' q
  have hdiv : ∀ u : ℂ, α * (u / α) = u := fun u => by field_simp
  classical
  haveI := Fintype.ofFinite (L.lattice ⧸ LinearMap.range (mulEnd L α h))
  refine ⟨(Finset.univ.filter (fun q : L.lattice ⧸ LinearMap.range (mulEnd L α h) => q ≠ 0)).image
    (fun q => ((Quotient.out q : L.lattice) : ℂ) / α), ?_⟩
  unfold IsKerReps
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨by rw [hdiv]; exact (Quotient.out q).2, ?_⟩
    intro hm
    apply hq
    rw [← hout q, ← Submodule.Quotient.mk_zero, mk_eq_iff]
    exact ⟨_, hm, by rw [hdiv]; simp⟩
  · intro P hP P' hP' hd
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hP'
    have hqq : q = q' := by
      rw [← hout q, ← hout q', mk_eq_iff]
      exact ⟨_, hd, by rw [mul_sub, hdiv, hdiv]⟩
    rw [hqq]
  · intro z hz hzn
    have hq0 : (Submodule.Quotient.mk (⟨α * z, hz⟩ : L.lattice) :
        L.lattice ⧸ LinearMap.range (mulEnd L α h)) ≠ 0 := by
      intro h0
      rw [← Submodule.Quotient.mk_zero, mk_eq_iff] at h0
      obtain ⟨x, hx, hxe⟩ := h0
      have hzx : z = x := by simpa [hα] using hxe
      exact hzn (hzx ▸ hx)
    set q : L.lattice ⧸ LinearMap.range (mulEnd L α h) := Submodule.Quotient.mk (⟨α * z, hz⟩ : L.lattice) with hqdef
    refine ⟨((Quotient.out q : L.lattice) : ℂ) / α, Finset.mem_image.2 ⟨q, by simp [hq0], rfl⟩, ?_⟩
    have h5 := hout q
    rw [hqdef, mk_eq_iff] at h5
    obtain ⟨x, hx, hxe⟩ := h5
    have hxe' : ((Quotient.out q : L.lattice) : ℂ) - α * z = α * x := hxe
    have hzx : z - ((Quotient.out q : L.lattice) : ℂ) / α = -x :=
      mul_left_cancel₀ hα (by rw [mul_sub, hdiv]; linear_combination -hxe')
    rw [hzx]
    exact neg_mem hx
end Formalism.L2.Th1.F
