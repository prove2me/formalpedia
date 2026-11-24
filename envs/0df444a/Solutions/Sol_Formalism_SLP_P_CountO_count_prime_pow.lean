-- Prove2me | solution 1 for Formalism.SLP.P.CountO.count_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:17:31.286409+00:00
-- url     : https://prove2.me/submissions/ab5a7f13-a5ba-4d2d-b9f3-3807d727390d

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Theorems.Thm_Formalism_SLP_P_CountO_primes_card
import Theorems.Thm_Formalism_SLP_P_CountO_exists_gen_mod
import Theorems.Thm_Formalism_SLP_P_CountO_card_hom_le
import Theorems.Thm_Formalism_SLP_P_CountO_hyp_count
import Theorems.Thm_Formalism_SLP_P_CountO_exists_hyp_above
import Theorems.Thm_Formalism_SLP_P_CountO_index_comap_mul
import Theorems.Thm_Formalism_SLP_P_CountO_TF_submodule
import Theorems.Thm_Formalism_SLP_P_CountO_LIB_submodule
import Theorems.Thm_Formalism_SLP_P_CountO_mem_of_card_dvd
import Theorems.Thm_Formalism_SLP_P_CountO_ncard_biUnion_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
open NumberField
variable (E : Type) [Field E] [NumberField E]
variable {E}
namespace Formalism.SLP.P.CountO
theorem _root_.solution (k p : ℕ) (hp : p.Prime) (e : ℕ) :
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X],
      TF E X → LIB E X k →
      (idxSet (𝓞 E) X (p ^ e)).Finite ∧
        (idxSet (𝓞 E) X (p ^ e)).ncard ≤ finrank ℚ E ^ e * (p ^ e) ^ k := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro X _ _ _ htf hli
  rcases Nat.eq_zero_or_pos e with rfl | he
  · have h1 : idxSet (𝓞 E) X (p ^ 0) = {⊤} := by
      ext N
      simp only [idxSet, pow_zero, Set.mem_ofPred_eq, AddSubgroup.index_eq_one,
        Set.mem_singleton_iff, Submodule.toAddSubgroup_eq_top]
    rw [h1]
    simp
  classical
  have : IsNoetherian (𝓞 E) X := isNoetherian_of_isNoetherianRing_of_finite _ _
  set n := finrank ℚ E with hn_def
  have hn : 0 < n := Module.finrank_pos
  obtain ⟨Ps, hPs, hPmem⟩ := primes_card E p hp
  let G : Finset (Ideal (𝓞 E)) :=
    Ps.filter (fun P => P.IsMaximal ∧ Nat.card (𝓞 E ⧸ P) ∣ p ^ e)
  have hGf : ∀ P ∈ G, ∃ f : ℕ, 1 ≤ f ∧ f ≤ e ∧ Nat.card (𝓞 E ⧸ P) = p ^ f := by
    intro P hP
    obtain ⟨_, hPm, hdvd⟩ := Finset.mem_filter.mp hP
    obtain ⟨f, hfe, hf⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    refine ⟨f, ?_, hfe, hf⟩
    rcases Nat.eq_zero_or_pos f with rfl | hf0
    · exfalso
      have : Nontrivial (𝓞 E ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hPm.ne_top
      have h2 : 1 < Nat.card (𝓞 E ⧸ P) := Finite.one_lt_card
      rw [hf, pow_zero] at h2
      exact lt_irrefl _ h2
    · exact hf0
  choose! f hf1 hfe hfc using hGf
  let A : Ideal (𝓞 E) → Submodule (𝓞 E) X → Set (Submodule (𝓞 E) X) :=
    fun P L => (Submodule.map L.subtype) '' idxSet (𝓞 E) L (p ^ (e - f P))
  have hhyp : ∀ P ∈ G, (hyp P X).Finite ∧ (hyp P X).ncard ≤ (p ^ f P) ^ k := by
    intro P hP
    have hPm : P.IsMaximal := (Finset.mem_filter.mp hP).2.1
    have hP0 : P ≠ ⊥ := (Ideal.bot_lt_of_maximal P (RingOfIntegers.not_isField E)).ne'
    obtain ⟨s, hsk, hs⟩ := exists_gen_mod P hP0 htf k hli
    have := hyp_count P k (card_hom_le P k s hsk hs)
    rw [hfc P hP] at this
    exact this
  have hA : ∀ P ∈ G, ∀ L ∈ hyp P X,
      (A P L).Finite ∧ (A P L).ncard ≤ n ^ (e - f P) * (p ^ (e - f P)) ^ k := by
    intro P hP L _
    have h := ih (e - f P) (by have := hf1 P hP; omega) L (htf.submodule L) (hli.submodule L)
    exact ⟨h.1.image _, (Set.ncard_image_le h.1).trans h.2⟩
  let H : Ideal (𝓞 E) → Finset (Submodule (𝓞 E) X) :=
    fun P => if h : P ∈ G then (hhyp P h).1.toFinset else ∅
  have hH : ∀ P ∈ G, ∀ L, L ∈ H P ↔ L ∈ hyp P X := by
    intro P hP L
    simp only [H, dif_pos hP, Set.Finite.mem_toFinset]
  have hHc : ∀ P ∈ G, (H P).card ≤ (p ^ f P) ^ k := by
    intro P hP
    simp only [H, dif_pos hP]
    rw [← Set.ncard_eq_toFinset_card _ (hhyp P hP).1]
    exact (hhyp P hP).2
  have hcover : idxSet (𝓞 E) X (p ^ e) ⊆ ⋃ P ∈ G, ⋃ L ∈ H P, A P L := by
    intro N hN
    have hN' : N.toAddSubgroup.index = p ^ e := hN
    have hNtop : N ≠ ⊤ := by
      rintro rfl
      have h1 : (⊤ : Submodule (𝓞 E) X).toAddSubgroup.index = 1 := by simp
      rw [hN'] at h1
      exact (Nat.one_lt_pow he.ne' hp.one_lt).ne' h1
    obtain ⟨P, hPm, L, hL, hNL⟩ := exists_hyp_above N hNtop
    have hdvd : Nat.card (𝓞 E ⧸ P) ∣ p ^ e := by
      rw [← hL.2, ← hN']
      exact AddSubgroup.index_dvd_of_le (Submodule.toAddSubgroup_mono hNL)
    have hPG : P ∈ G := Finset.mem_filter.mpr ⟨hPmem P hPm (mem_of_card_dvd hdvd), hPm, hdvd⟩
    have hrel : (N.comap L.subtype).toAddSubgroup.index = p ^ (e - f P) := by
      have h1 := index_comap_mul N L hNL
      rw [hL.2, hfc P hPG, hN'] at h1
      have h2 : p ^ (e - f P) * p ^ f P = p ^ e := by
        rw [← pow_add, Nat.sub_add_cancel (hfe P hPG)]
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) (h1.trans h2.symm)
    have hmemA : N ∈ A P L := by
      refine ⟨N.comap L.subtype, hrel, ?_⟩
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hNL]
    exact Set.mem_iUnion₂.mpr ⟨P, hPG, Set.mem_iUnion₂.mpr ⟨L, (hH P hPG L).mpr hL, hmemA⟩⟩
  have hinner : ∀ P ∈ G, (⋃ L ∈ H P, A P L).Finite ∧
      (⋃ L ∈ H P, A P L).ncard ≤ n ^ (e - 1) * (p ^ e) ^ k := by
    intro P hP
    obtain ⟨hfin, hle⟩ := ncard_biUnion_le (H P) (A P)
      (fun L hL => (hA P hP L ((hH P hP L).mp hL)).1)
    refine ⟨hfin, hle.trans ?_⟩
    calc ∑ L ∈ H P, (A P L).ncard ≤ ∑ _L ∈ H P, n ^ (e - f P) * (p ^ (e - f P)) ^ k :=
          Finset.sum_le_sum fun L hL => (hA P hP L ((hH P hP L).mp hL)).2
      _ = (H P).card * (n ^ (e - f P) * (p ^ (e - f P)) ^ k) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (p ^ f P) ^ k * (n ^ (e - f P) * (p ^ (e - f P)) ^ k) :=
          Nat.mul_le_mul_right _ (hHc P hP)
      _ = n ^ (e - f P) * (p ^ e) ^ k := by
          rw [mul_left_comm, ← mul_pow, ← pow_add, Nat.add_sub_cancel' (hfe P hP)]
      _ ≤ n ^ (e - 1) * (p ^ e) ^ k :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn (by have := hf1 P hP; omega))
  obtain ⟨hfinU, hleU⟩ := ncard_biUnion_le G (fun P => ⋃ L ∈ H P, A P L)
    (fun P hP => (hinner P hP).1)
  refine ⟨hfinU.subset hcover, (Set.ncard_le_ncard hcover hfinU).trans (hleU.trans ?_)⟩
  calc ∑ P ∈ G, (⋃ L ∈ H P, A P L).ncard ≤ ∑ _P ∈ G, n ^ (e - 1) * (p ^ e) ^ k :=
        Finset.sum_le_sum fun P hP => (hinner P hP).2
    _ = G.card * (n ^ (e - 1) * (p ^ e) ^ k) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * (n ^ (e - 1) * (p ^ e) ^ k) :=
        Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hPs)
    _ = n ^ e * (p ^ e) ^ k := by
        rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel he]
end Formalism.SLP.P.CountO
