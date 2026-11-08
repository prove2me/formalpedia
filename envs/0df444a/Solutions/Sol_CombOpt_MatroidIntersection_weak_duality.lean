-- Prove2me | solution 1 for CombOpt.MatroidIntersection.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:46:31.494167+00:00
-- url     : https://prove2.me/submissions/5d070f85-7187-4dc2-8b81-2a11ce027cce

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersection_Matroid
import Definitions.Def_CombOpt_MatroidIntersection_rank

namespace Aux_MIWeakDual

theorem key {S : Type*} [DecidableEq S] (Indep : Finset S → Prop)
    (A K : Finset S) (hKA : K ⊆ A) (hK : Indep K) :
    K.card ≤ CombOpt.MatroidIntersection.rank Indep A := by
  classical
  let C := A.powerset.filter (fun I => K ⊆ I ∧ Indep I)
  have hne : C.Nonempty := ⟨K, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hKA, le_rfl, hK⟩⟩
  obtain ⟨I, hIC, hImax⟩ := C.exists_max_image Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hIC
  have hmax : EdmondsPartition.Main.IsMaxIndepIn Indep A I := by
    refine ⟨hIC.1, hIC.2.2, fun J hIJ hJA hJ => ?_⟩
    have hJC : J ∈ C := Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hJA, hIC.2.1.trans hIJ, hJ⟩
    exact (Finset.eq_of_subset_of_card_le hIJ (hImax J hJC)).symm
  calc K.card ≤ I.card := Finset.card_le_card hIC.2.1
    _ ≤ CombOpt.MatroidIntersection.rank Indep A := by
      unfold CombOpt.MatroidIntersection.rank
      exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hIC.1, hmax⟩)

end Aux_MIWeakDual

open CombOpt.MatroidIntersection in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : CombOpt.MatroidIntersection.Matroid S)
    (J A : Finset S) (hJ₁ : M₁.Indep J) (hJ₂ : M₂.Indep J) :
    J.card ≤ CombOpt.MatroidIntersection.rank M₁.Indep A +
      CombOpt.MatroidIntersection.rank M₂.Indep Aᶜ := by
  have h1 := Aux_MIWeakDual.key M₁.Indep A (J ∩ A) Finset.inter_subset_right
    (M₁.isMatroid.2.1 _ _ Finset.inter_subset_left hJ₁)
  have h2 := Aux_MIWeakDual.key M₂.Indep Aᶜ (J \ A)
    (fun x hx => by
      rw [Finset.mem_sdiff] at hx
      exact Finset.mem_compl.2 hx.2)
    (M₂.isMatroid.2.1 _ _ Finset.sdiff_subset hJ₂)
  have hc := Finset.card_inter_add_card_sdiff J A
  omega
