-- Prove2me | solution 1 for Formalism.SLP.P.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:49:05.456935+00:00
-- url     : https://prove2.me/submissions/e643564b-73b6-4790-9b13-a56fed819845

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount
import Theorems.Thm_Formalism_SLP_P_index_prod_eq
import Theorems.Thm_Formalism_SLP_P_eq_zmultiples_index
import Theorems.Thm_Formalism_SLP_P_le_of_lifts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.P
open AddSubgroup
namespace Formalism.SLP.P
theorem _root_.solution {A : Type*} [AddCommGroup A] (n : ℕ)
    (hgen : ∀ K : AddSubgroup A, ∃ v : Fin n → A, AddSubgroup.closure (Set.range v) = K)
    (ih : ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup A | H.index = j}.Finite ∧
      {H : AddSubgroup A | H.index = j}.ncard ≤ j ^ n) :
    ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup (ℤ × A) | H.index = j}.Finite ∧
      {H : AddSubgroup (ℤ × A) | H.index = j}.ncard ≤ j ^ (n + 1) := by
  intro j hj
  choose V hV using hgen
  classical
  set S := {H : AddSubgroup (ℤ × A) | H.index = j} with hS
  let dd : AddSubgroup (ℤ × A) → ℕ := fun H => (H.comap (AddMonoidHom.inl ℤ A)).index
  let cc : AddSubgroup (ℤ × A) → Fin n → ℤ := fun H i =>
    if h : ∃ x : ℤ, (x, V (H.map (AddMonoidHom.snd ℤ A)) i) ∈ H then h.choose % (dd H : ℤ)
    else 0
  let F : AddSubgroup (ℤ × A) → ℕ × AddSubgroup A × (Fin n → ℤ) :=
    fun H => (dd H, H.map (AddMonoidHom.snd ℤ A), cc H)
  let cube : ℕ → Finset (Fin n → ℤ) := fun d => Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) d
  let T : Set (ℕ × AddSubgroup A × (Fin n → ℤ)) :=
    ⋃ d ∈ j.divisors, ({d} : Set ℕ) ×ˢ ({H : AddSubgroup A | H.index = j / d} ×ˢ
      (cube d : Set (Fin n → ℤ)))
  have hpos : ∀ H ∈ S, 0 < dd H ∧ H.index = dd H * (H.map (AddMonoidHom.snd ℤ A)).index := by
    intro H hH
    have hp := index_prod_eq H
    refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, hp⟩
    have : H.index = j := hH
    simp only [dd] at h0
    rw [h0, zero_mul] at hp
    omega
  have hmaps : ∀ H ∈ S, F H ∈ T := by
    intro H hH
    obtain ⟨hd, hp⟩ := hpos H hH
    have hHj : H.index = j := hH
    simp only [T, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    refine ⟨dd H, Nat.mem_divisors.mpr ⟨⟨_, hHj ▸ hp⟩, by omega⟩, rfl, ?_, ?_⟩
    · show (H.map (AddMonoidHom.snd ℤ A)).index = j / dd H
      rw [← hHj, hp, Nat.mul_div_cancel_left _ hd]
    · simp only [cube]
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro i
      simp only [F, cc, Finset.mem_Ico]
      have hd' : (0 : ℤ) < (dd H : ℤ) := by exact_mod_cast hd
      split_ifs
      · exact ⟨Int.emod_nonneg _ hd'.ne', Int.emod_lt_of_pos _ hd'⟩
      · exact ⟨le_rfl, hd'⟩
  have hinj : Set.InjOn F S := by
    intro H₁ hH₁ H₂ hH₂ hF
    simp only [F, Prod.mk.injEq] at hF
    obtain ⟨hd, hm, hc⟩ := hF
    have hD₁ := eq_zmultiples_index (H₁.comap (AddMonoidHom.inl ℤ A))
    have hD₂ := eq_zmultiples_index (H₂.comap (AddMonoidHom.inl ℤ A))
    have hDD : H₁.comap (AddMonoidHom.inl ℤ A) = H₂.comap (AddMonoidHom.inl ℤ A) := by
      rw [hD₁, hD₂]
      exact congrArg (fun d : ℕ => zmultiples (d : ℤ)) hd
    set v := V (H₁.map (AddMonoidHom.snd ℤ A)) with hvdef
    have hlift : ∀ i, ∃ x : ℤ, (x, v i) ∈ H₁ ⊓ H₂ := by
      intro i
      have hvi : v i ∈ H₁.map (AddMonoidHom.snd ℤ A) := by
        rw [← hV (H₁.map (AddMonoidHom.snd ℤ A))]
        exact subset_closure ⟨i, rfl⟩
      have hex₁ : ∃ x : ℤ, (x, V (H₁.map (AddMonoidHom.snd ℤ A)) i) ∈ H₁ := by
        obtain ⟨p, hp, hps⟩ := hvi
        exact ⟨p.1, by rw [← hvdef, ← hps]; exact hp⟩
      have hex₂ : ∃ x : ℤ, (x, V (H₂.map (AddMonoidHom.snd ℤ A)) i) ∈ H₂ := by
        rw [hm] at hvi
        obtain ⟨p, hp, hps⟩ := hvi
        exact ⟨p.1, by rw [← hm, ← hvdef, ← hps]; exact hp⟩
      have hci := congrFun hc i
      simp only [cc, dif_pos hex₁, dif_pos hex₂] at hci
      have hs₁ := hex₁.choose_spec
      have hkey : ∀ x : ℤ, (x, V (H₂.map (AddMonoidHom.snd ℤ A)) i) ∈ H₂ → (x, v i) ∈ H₂ :=
        fun x hx => by rw [hvdef, hm]; exact hx
      have hs₂ := hkey _ hex₂.choose_spec
      refine ⟨hex₁.choose, hs₁, ?_⟩
      have hmod : (dd H₂ : ℤ) ∣ hex₂.choose - hex₁.choose := by
        rw [hd] at hci
        exact Int.ModEq.dvd hci
      have hz : hex₂.choose - hex₁.choose ∈ H₂.comap (AddMonoidHom.inl ℤ A) := by
        rw [hD₂]
        exact Int.mem_zmultiples_iff.mpr hmod
      have hz' : (hex₂.choose - hex₁.choose, (0 : A)) ∈ H₂ := hz
      have he : (hex₁.choose, v i) =
          (hex₂.choose, v i) - (hex₂.choose - hex₁.choose, (0 : A)) := by
        ext
        · simp
        · simp
      rw [he]
      exact H₂.sub_mem hs₂ hz'
    apply le_antisymm
    · exact le_of_lifts v (hV _) hDD.le hlift
    · refine le_of_lifts v (by rw [← hm]; exact hV _) hDD.ge fun i => ?_
      obtain ⟨x, hx⟩ := hlift i
      exact ⟨x, by rwa [inf_comm]⟩
  have hTfin : T.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun d hd => ?_
    refine (Set.finite_singleton d).prod ((ih _ ?_).1.prod (Finset.finite_toSet _))
    exact Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
  refine ⟨Set.Finite.of_finite_image (hTfin.subset ?_) hinj, ?_⟩
  · rintro _ ⟨H, hH, rfl⟩
    exact hmaps H hH
  calc S.ncard ≤ T.ncard := Set.ncard_le_ncard_of_injOn F hmaps hinj hTfin
    _ ≤ ∑ d ∈ j.divisors, (({d} : Set ℕ) ×ˢ ({H : AddSubgroup A | H.index = j / d} ×ˢ
          (cube d : Set (Fin n → ℤ)))).ncard := Finset.set_ncard_biUnion_le _ _
    _ = ∑ d ∈ j.divisors, {H : AddSubgroup A | H.index = j / d}.ncard * d ^ n := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Set.ncard_prod, Set.ncard_prod, Set.ncard_singleton, one_mul, Set.ncard_coe_finset]
        simp [cube, Fintype.card_piFinset, Int.card_Ico]
    _ ≤ ∑ d ∈ j.divisors, (j / d) ^ n * d ^ n := by
        refine Finset.sum_le_sum fun d hd => Nat.mul_le_mul_right _ (ih _ ?_).2
        exact Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
    _ = ∑ _d ∈ j.divisors, j ^ n := by
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [← mul_pow, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
    _ = j.divisors.card * j ^ n := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ j * j ^ n := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self j)
    _ = j ^ (n + 1) := by ring
end Formalism.SLP.P
