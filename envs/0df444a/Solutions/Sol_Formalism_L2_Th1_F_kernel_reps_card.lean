-- Prove2me | solution 1 for Formalism.L2.Th1.F.kernel_reps_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:53:02.243715+00:00
-- url     : https://prove2.me/submissions/9eb578e3-b232-4939-97e2-d62fac11b6d5

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
theorem _root_.solution : KerRepsCard := by
  unfold KerRepsCard
  intro L α S hα h hS
  obtain ⟨h1, h2, h3⟩ := hS
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
  have hφ0 : ∀ P : S, (Submodule.Quotient.mk (⟨α * P, (h1 P P.2).1⟩ : L.lattice) :
      L.lattice ⧸ LinearMap.range (mulEnd L α h)) ≠ 0 := by
    intro P h0
    rw [← Submodule.Quotient.mk_zero, mk_eq_iff] at h0
    obtain ⟨x, hx, hxe⟩ := h0
    have hPx : (P : ℂ) = x := by simpa [hα] using hxe
    exact (h1 P P.2).2 (hPx ▸ hx)
  let φ : S → {q : L.lattice ⧸ LinearMap.range (mulEnd L α h) // ¬ q = 0} :=
    fun P => ⟨Submodule.Quotient.mk (⟨α * P, (h1 P P.2).1⟩ : L.lattice), hφ0 P⟩
  have hinj : Function.Injective φ := by
    intro P P' hPP
    have h6 := congrArg Subtype.val hPP
    simp only [φ] at h6
    rw [mk_eq_iff] at h6
    obtain ⟨x, hx, hxe⟩ := h6
    have hxe' : α * (P : ℂ) - α * (P' : ℂ) = α * x := hxe
    have hd : (P : ℂ) - P' = x := mul_left_cancel₀ hα (by rw [mul_sub]; exact hxe')
    exact Subtype.ext (h2 P P.2 P' P'.2 (hd ▸ hx))
  have hsurj : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    have hz1 : α * (((Quotient.out q : L.lattice) : ℂ) / α) ∈ L.lattice := by
      rw [hdiv]; exact (Quotient.out q).2
    have hz2 : ((Quotient.out q : L.lattice) : ℂ) / α ∉ L.lattice := by
      intro hm
      apply hq
      rw [← hout q, ← Submodule.Quotient.mk_zero, mk_eq_iff]
      exact ⟨_, hm, by rw [hdiv]; simp⟩
    obtain ⟨P, hP, hzP⟩ := h3 _ hz1 hz2
    refine ⟨⟨P, hP⟩, Subtype.ext ?_⟩
    show (Submodule.Quotient.mk (⟨α * P, (h1 P hP).1⟩ : L.lattice) :
      L.lattice ⧸ LinearMap.range (mulEnd L α h)) = q
    conv_rhs => rw [← hout q]
    rw [mk_eq_iff]
    refine ⟨-(((Quotient.out q : L.lattice) : ℂ) / α - P), neg_mem hzP, ?_⟩
    show α * (P : ℂ) - ((Quotient.out q : L.lattice) : ℂ) = _
    rw [mul_neg, mul_sub, hdiv]
    ring
  have hcard : Nat.card S = Nat.card {q : L.lattice ⧸ LinearMap.range (mulEnd L α h) // ¬ q = 0} :=
    Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)
  have hc1 : Nat.card {q : L.lattice ⧸ LinearMap.range (mulEnd L α h) // ¬ q = 0} + 1 =
      Nat.card (L.lattice ⧸ LinearMap.range (mulEnd L α h)) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have := Fintype.card_pos (α := L.lattice ⧸ LinearMap.range (mulEnd L α h))
    omega
  have e2 : Nat.card S = S.card := by simp
  rw [← card_quot L α hα h]
  exact_mod_cast (show S.card + 1 = Nat.card (L.lattice ⧸ LinearMap.range (mulEnd L α h)) by
    rw [← e2, hcard, hc1])
end Formalism.L2.Th1.F
