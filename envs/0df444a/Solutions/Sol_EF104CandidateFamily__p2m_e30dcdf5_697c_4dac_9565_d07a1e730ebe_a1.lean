-- Prove2me | solution 1 for EF104CandidateFamily__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T16:30:27.107183+00:00
-- url     : https://prove2.me/submissions/cb3c5128-fba0-4da7-ae3c-041d0f9aa16a

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
import Theorems.Thm_EnvyFreeCake104_Divide_trimAgainst_largest_admissible_suffix__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
import Theorems.Thm_EnvyFreeCake104_Divide_candidate_history_rule__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1

open EnvyFreeCake104.Divide

namespace CFAux

theorem guess_facts {ι : Type} [DecidableEq ι] (N : Finset ι) (g : List ι × List ι)
    (hg : g ∈ guesses N) :
    g.1.Nodup ∧ (∀ q ∈ g.1.zip g.2, q.1 ∈ N ∧ q.2 ∈ N) ∧
      ∀ i ∈ N, ∃ q ∈ g.1.zip g.2, q.1 = i := by
  obtain ⟨l1, l2⟩ := g
  unfold guesses at hg
  rw [List.pair_mem_product, List.mem_permutations, List.mem_permutations] at hg
  obtain ⟨h1, h2⟩ := hg
  refine ⟨h1.nodup_iff.mpr (Finset.nodup_toList N), fun q hq => ?_, fun i hi => ?_⟩
  · have := List.of_mem_zip hq
    exact ⟨by rw [← Finset.mem_toList, ← h1.mem_iff]; exact this.1,
      by rw [← Finset.mem_toList, ← h2.mem_iff]; exact this.2⟩
  · have hi1 : i ∈ l1 := by rw [h1.mem_iff, Finset.mem_toList]; exact hi
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi1
    have hk2 : k < l2.length := by rw [h2.length_eq, ← h1.length_eq]; exact hk
    have hkz : k < (l1.zip l2).length := by simp [List.length_zip]; omega
    exact ⟨(l1.zip l2)[k], List.getElem_mem hkz, by simp [List.getElem_zip]⟩

/-- A valid record state in which every piece of `N` is aligned. -/
theorem exists_valid {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF) :
    ∃ t : Rec ι, t.Valid V N ∧ ∀ i ∈ N, t.Aligned (P i) := by
  classical
  let E : Finset ℝ := N.biUnion (fun i => ((P i).map (fun I => I.a) ++ (P i).map (fun I => I.b)).toFinset)
  let pts : Finset ℝ := insert 0 (insert 1 E)
  let t0 : Rec ι := ⟨pts, fun _ _ => 0, 0⟩
  let t : Rec ι := ⟨pts, fun i c => (V i).value (Set.Ico c (t0.nextPt c)), 0⟩
  have hnext : ∀ c, t.nextPt c = t0.nextPt c := fun c => rfl
  refine ⟨t, ⟨by simp [t, pts], by simp [t, pts], ?_, ?_⟩, ?_⟩
  · intro c hc
    simp only [t, pts, Finset.mem_insert, E, Finset.mem_biUnion, List.mem_toFinset,
      List.mem_append, List.mem_map] at hc
    rcases hc with rfl | rfl | ⟨i, hi, ⟨I, hI, rfl⟩ | ⟨I, hI, rfl⟩⟩
    · norm_num
    · norm_num
    · have := (hP i hi).1 I hI; exact ⟨this.1, this.2.1.trans this.2.2⟩
    · have := (hP i hi).1 I hI; exact ⟨this.1.trans this.2.1, this.2.2⟩
  · intro i _ c _ _; rw [hnext]
  · intro i hi I hI
    constructor <;> simp only [t, pts, Finset.mem_insert, E, Finset.mem_biUnion,
      List.mem_toFinset, List.mem_append, List.mem_map]
    · exact Or.inr (Or.inr ⟨i, hi, Or.inl ⟨I, hI, rfl⟩⟩)
    · exact Or.inr (Or.inr ⟨i, hi, Or.inr ⟨I, hI, rfl⟩⟩)

/-- Every successful candidate run produces the greedy profile. -/
theorem run_greedy {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF) (g : List ι × List ι) (hg : g ∈ guesses N)
    (t : Rec ι) (ht : t.Valid V N) (hPt : ∀ i ∈ N, t.Aligned (P i)) (q : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (R : Piece) (u : Rec ι) (tr : List (Event ι)),
      exec V q (candidate N P g.1 g.2) t = some ((Y, R), u, tr) ∧
      EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1 V P g.1 g.2
        (fun i => (Y i).toSet) := by
  obtain ⟨hnd, hmem, -⟩ := guess_facts N g hg
  let K : List ι → (ι → Piece) → Piece → Piece → Prop := fun earlier Y Q B =>
    IsSuffix B.toSet Q ∧ (∀ i ∈ earlier, (V i).value B.toSet ≤ (V i).value (Y i).toSet) ∧
      ∀ S : Set ℝ, IsSuffix S Q → (∀ i ∈ earlier, (V i).value S ≤ (V i).value (Y i).toSet) →
        S ⊆ B.toSet
  have hstable : ∀ (earlier : List ι) (Y Z : ι → Piece) (Q B : Piece),
      (∀ i ∈ earlier, Y i = Z i) → K earlier Y Q B → K earlier Z Q B := by
    intro earlier Y Z Q B hYZ ⟨h1, h2, h3⟩
    refine ⟨h1, fun i hi => hYZ i hi ▸ h2 i hi, fun S hS hle => h3 S hS ?_⟩
    intro i hi; rw [hYZ i hi]; exact hle i hi
  have htrim : ∀ (Y : ι → Piece) (earlier : List ι) (Q : Piece) (s : Rec ι),
      (∀ i ∈ N, (Y i).WF) → (∀ i ∈ earlier, i ∈ N) →
      Q.WF → s.Valid V N →
      (∀ i ∈ N, s.Aligned (Y i)) → s.Aligned Q →
      ∀ (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      ∃ (B rem : Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((trimAgainst N Y earlier Q []).run s) tr₀ =
          some (((B, rem), s'), tr) ∧
        s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ B.WF ∧ s'.Aligned B ∧ K earlier Y Q B := by
    intro Y earlier Q s hY hear hQ hs hYs hQs o tr₀
    obtain ⟨B, rem, s', tr, hr, h1, h2, h3, h4, h5, h6, h7⟩ :=
      trimAgainst_largest_admissible_suffix__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1 V N
        (fun i hi Q hQ s hs hQs w hw hwQ o tr₀ =>
          prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2 V N i hi Q hQ s hs
            hQs w hw hwQ o tr₀)
        Y hY earlier hear Q [] hQ s hs hYs hQs o tr₀
    exact ⟨B, rem, s', tr, hr, h1, h2, h3, h4, h5, h6, fun S hS hle => (h7 S hS hle).1⟩
  obtain ⟨Y, R, u, tr, hex, hK⟩ :=
    candidate_history_rule__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1 V N K hstable htrim P hP t
      ht hPt g.1 g.2 hnd hmem q
  refine ⟨Y, R, u, tr, hex, ?_⟩
  intro before p after hz
  obtain ⟨h1, h2, h3⟩ := hK before p after hz
  refine ⟨h1, fun q hq => h2 q.1 (List.mem_map_of_mem hq), fun S hS hle => h3 S hS ?_⟩
  intro i hi
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
  exact hle q hq

/-- The greedy profile is unique on the agents of the guess. -/
theorem greedy_unique {ι : Type} (V : ι → Valuation) (P : ι → Piece) (ag pc : List ι)
    (A A' : ι → Set ℝ)
    (hA : EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1 V P ag pc A)
    (hA' : EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1 V P ag pc A') :
    ∀ p ∈ ag.zip pc, A p.1 = A' p.1 := by
  have key : ∀ n : ℕ, ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
      ag.zip pc = before ++ p :: after → before.length = n → A p.1 = A' p.1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro before p after hz hlen
      have hqe : ∀ q ∈ before, A q.1 = A' q.1 := by
        intro q hq
        obtain ⟨b1, b2, rfl⟩ := List.append_of_mem hq
        exact ih b1.length (by simp at hlen; omega) b1 q (b2 ++ p :: after)
          (by rw [hz]; simp) rfl
      obtain ⟨a1, a2, a3⟩ := hA before p after hz
      obtain ⟨b1, b2, b3⟩ := hA' before p after hz
      apply Set.Subset.antisymm
      · exact b3 (A p.1) a1 (fun q hqm => by rw [← hqe q hqm]; exact a2 q hqm)
      · exact a3 (A' p.1) b1 (fun q hqm => by rw [hqe q hqm]; exact b2 q hqm)
  intro p hp
  obtain ⟨before, after, hz⟩ := List.append_of_mem hp
  exact key _ before p after hz rfl

end CFAux

open CFAux in
theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF) :
    ∃ C : (List ι × List ι) → ι → Set ℝ,
      ∀ g ∈ guesses N,
        EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1 V P g.1 g.2 (C g) ∧
        ∀ (t : Rec ι), t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
          ∀ q : ChoiceOracle ι,
            ∃ (Y : ι → Piece) (R : Piece) (u : Rec ι) (tr : List (Event ι)),
              exec V q (candidate N P g.1 g.2) t = some ((Y, R), u, tr) ∧
              ∀ i ∈ N, (Y i).toSet = C g i := by
  classical
  obtain ⟨t0, ht0, hPt0⟩ := exists_valid V N P hP
  let C : (List ι × List ι) → ι → Set ℝ := fun g =>
    if hg : g ∈ guesses N then
      fun i => ((Classical.choose (run_greedy V N P hP g hg t0 ht0 hPt0 (fun _ _ => 0))) i).toSet
    else fun _ => ∅
  refine ⟨C, fun g hg => ?_⟩
  have hC : C g = fun i =>
      ((Classical.choose (run_greedy V N P hP g hg t0 ht0 hPt0 (fun _ _ => 0))) i).toSet := by
    simp only [C, dif_pos hg]
  obtain ⟨R0, u0, tr0, -, hGP0⟩ :=
    Classical.choose_spec (run_greedy V N P hP g hg t0 ht0 hPt0 (fun _ _ => 0))
  refine ⟨hC ▸ hGP0, fun t ht hPt q => ?_⟩
  obtain ⟨Y, R, u, tr, hex, hGP⟩ := run_greedy V N P hP g hg t ht hPt q
  refine ⟨Y, R, u, tr, hex, fun i hi => ?_⟩
  obtain ⟨-, -, hcov⟩ := guess_facts N g hg
  obtain ⟨p, hp, rfl⟩ := hcov i hi
  rw [hC]
  exact greedy_unique V P g.1 g.2 _ _ hGP hGP0 p hp
