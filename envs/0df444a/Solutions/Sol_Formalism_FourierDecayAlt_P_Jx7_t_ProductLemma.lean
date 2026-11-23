-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_ProductLemma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:15.727118+00:00
-- url     : https://prove2.me/submissions/e6154463-ff78-4213-b353-85577ca21e31

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder ComplexConjugate Matrix
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution (hS : SchurProduct) (hD : ProductDomination) : ProductLemma := by
  classical
  intro E α P _ _ S F hok
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' ht ht' h hh h' hh' hne
    simp only [prodSys] at hne ⊢
    rw [AddSubgroup.mem_iInf]
    intro p
    exact (hok p).1 t t' ht ht' h hh h' hh' (fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ p) h0))
  · intro t ht
    exact hS α P F (fun p => (S p).N t t) (fun p => (hok p).2.1 t ht)
  · intro t t' htt h hh h' hh'
    simp only [prodSys] at htt ⊢
    rw [AddSubgroup.mem_iInf] at htt
    exact Finset.prod_congr rfl (fun p _ => (hok p).2.2.1 t t' (htt p) h hh h' hh')
  · intro t
    exact hS α P F (fun p => (S p).Th t) (fun p => (hok p).2.2.2.1 t)
  · intro t ht
    exact hD α P F (fun p => (S p).N t t) (fun p => (S p).Th t) (fun p => (hok p).2.1 t ht)
      (fun p => (hok p).2.2.2.2.1 t ht)
  · intro R hR
    simp only [prodSys] at hR ⊢

    let ρ : P → E → E := fun p t => ((t : E ⧸ (S p).L)).out
    have hρ : ∀ p t, t - ρ p t ∈ (S p).L := by
      intro p t
      have h1 : ((ρ p t : E) : E ⧸ (S p).L) = (t : E ⧸ (S p).L) := Quotient.out_eq' _
      have h2 := (QuotientAddGroup.eq (s := (S p).L)).1 h1
      have : t - ρ p t = -ρ p t + t := by abel
      rw [this]; exact h2
    have hρeq : ∀ p t t', ρ p t - ρ p t' ∈ (S p).L → ρ p t = ρ p t' := by
      intro p t t' h
      have h1 : ((ρ p t : E) : E ⧸ (S p).L) = ((ρ p t' : E) : E ⧸ (S p).L) := by
        rw [QuotientAddGroup.eq]
        have : -ρ p t + ρ p t' = -(ρ p t - ρ p t') := by abel
        rw [this]; exact neg_mem h
      have h2 : ((ρ p t : E) : E ⧸ (S p).L) = (t : E ⧸ (S p).L) := Quotient.out_eq' _
      have h3 : ((ρ p t' : E) : E ⧸ (S p).L) = (t' : E ⧸ (S p).L) := Quotient.out_eq' _
      show ((t : E ⧸ (S p).L)).out = ((t' : E ⧸ (S p).L)).out
      rw [← h2, ← h3, h1]
    let T : P → Finset E := fun p => R.image (ρ p)
    let ι : E → (P → E) := fun t p => ρ p t
    have hιinj : Set.InjOn ι R := by
      intro t ht t' ht' h
      apply hR t ht t' ht'
      rw [AddSubgroup.mem_iInf]
      intro p
      have h1 : ρ p t = ρ p t' := congrFun h p
      have h2 := hρ p t
      have h3 := hρ p t'
      have : t - t' = (t - ρ p t) - (t' - ρ p t') := by rw [h1]; abel
      rw [this]; exact sub_mem h2 h3
    have hιmem : R.image ι ⊆ Fintype.piFinset T := by
      intro τ hτ
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hτ
      exact Fintype.mem_piFinset.2 (fun p => Finset.mem_image_of_mem _ ht)
    have hTinc : ∀ p, ∀ x ∈ T p, ∀ y ∈ T p, x - y ∈ (S p).L → x = y := by
      intro p x hx y hy hxy
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨t', _, rfl⟩ := Finset.mem_image.1 hy
      exact hρeq p t t' hxy

    have hA : TB.PSDOn F (fun h h' => ∏ p, (S p).B h h' - ∏ p, ∑ x ∈ T p, (S p).Th x h h') :=
      hD α P F (fun p h h' => ∑ x ∈ T p, (S p).Th x h h') (fun p => (S p).B)
        (fun p => psd_sum (T p) (fun x => (S p).Th x) (fun x _ => (hok p).2.2.2.1 x))
        (fun p => (hok p).2.2.2.2.2 (T p) (hTinc p))

    have hB : ∀ Q : Finset (P → E), TB.PSDOn F (fun h h' => ∑ τ ∈ Q, ∏ p, (S p).Th (τ p) h h') := by
      intro Q
      apply psd_sum Q (fun τ h h' => ∏ p, (S p).Th (τ p) h h')
      intro τ _
      exact hS α P F (fun p => (S p).Th (τ p)) (fun p => (hok p).2.2.2.1 (τ p))
    refine psd_congr ?_ (psd_add hA (hB (Fintype.piFinset T \ R.image ι)))
    intro h hh h' hh'
    have h1 : ∑ t ∈ R, ∏ p, (S p).Th t h h' = ∑ τ ∈ R.image ι, ∏ p, (S p).Th (τ p) h h' := by
      rw [Finset.sum_image hιinj]
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.prod_congr rfl (fun p _ => (hok p).2.2.1 t (ρ p t) (hρ p t) h hh h' hh')
    have h2 : ∏ p, ∑ x ∈ T p, (S p).Th x h h' = ∑ τ ∈ Fintype.piFinset T, ∏ p, (S p).Th (τ p) h h' :=
      Finset.prod_univ_sum T (fun p x => (S p).Th x h h')
    have h3 := Finset.sum_sdiff (f := fun τ => ∏ p, (S p).Th (τ p) h h') hιmem
    rw [h1, h2, ← h3]
    ring
end Formalism.FourierDecayAlt.P.Jx7
