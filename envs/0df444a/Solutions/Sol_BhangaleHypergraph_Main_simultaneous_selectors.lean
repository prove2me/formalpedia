-- Prove2me | solution 1 for BhangaleHypergraph.Main.simultaneous_selectors
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T05:45:57.183295+00:00
-- url     : https://prove2.me/submissions/c4ad2934-7b3f-474b-9c66-aca12ac5044d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BhangaleHypergraph_Main_avoiding_amplification
import Theorems.Thm_BhangaleHypergraph_Main_avoiding_minor

open BhangaleHypergraph.Main

namespace SelectorProof

open Finset

lemma core_testDomain {C : ℕ} (f : CoreColoring C) : TestDomain f.W := by
  constructor
  · apply f.core_subset
    simp [Core]
  · apply f.core_subset
    simp [Core]

lemma core_mono {C R s s' : ℕ} (h : s ≤ s') :
    Core C s R ⊆ Core C s' R := by
  intro X hX
  simp only [Core, Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
  rcases hX with hX | hX | hX
  · exact Or.inl (hX.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (C + 1) h) C))
  · exact Or.inr (Or.inl (hX.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left (C + 1) h) C)))
  · rcases hX with ⟨P, hP, A, hA, H, hX, hH⟩
    exact Or.inr (Or.inr ⟨P, hP.trans (Nat.mul_le_mul_left (C + 1) h), A, hA, H, hX, hH⟩)

lemma exists_maximal_disjoint_subfamily {ι : Type} [DecidableEq ι]
    (A : Finset (Finset ι)) (hA : ∀ S ∈ A, S.Nonempty) :
    ∃ P : Finset (Finset ι),
      P ⊆ A ∧
      (∀ S ∈ P, ∀ U ∈ P, S ≠ U → Disjoint S U) ∧
      ∀ S ∈ A, (S ∩ P.biUnion (fun U => U)).Nonempty := by
  classical
  let Good : Finset (Finset ι) → Prop := fun P =>
    ∀ S ∈ P, ∀ U ∈ P, S ≠ U → Disjoint S U
  let Fs : Finset (Finset (Finset ι)) := A.powerset.filter Good
  have hFs : Fs.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [Fs, Good]
  obtain ⟨P, hPF, hPmax⟩ := Finset.exists_max_image Fs Finset.card hFs
  have hPmem := Finset.mem_filter.mp hPF
  have hPA : P ⊆ A := Finset.mem_powerset.mp hPmem.1
  have hPgood : Good P := hPmem.2
  refine ⟨P, hPA, hPgood, ?_⟩
  intro S hS
  by_contra hno
  have hdis : ∀ U ∈ P, Disjoint S U := by
    intro U hU
    rw [Finset.disjoint_left]
    intro a haS haU
    apply hno
    exact ⟨a, Finset.mem_inter.mpr ⟨haS, Finset.mem_biUnion.mpr ⟨U, hU, haU⟩⟩⟩
  have hSP : S ∉ P := by
    intro hSP
    obtain ⟨a, ha⟩ := hA S hS
    apply hno
    exact ⟨a, Finset.mem_inter.mpr ⟨ha, Finset.mem_biUnion.mpr ⟨S, hSP, ha⟩⟩⟩
  have hinsA : insert S P ⊆ A := Finset.insert_subset hS hPA
  have hinsGood : Good (insert S P) := by
    intro U hU V hV hUV
    simp only [Finset.mem_insert] at hU hV
    rcases hU with rfl | hU
    · rcases hV with rfl | hV
      · exact (hUV rfl).elim
      · exact hdis V hV
    · rcases hV with rfl | hV
      · exact (hdis U hU).symm
      · exact hPgood U hU V hV hUV
  have hinsF : insert S P ∈ Fs := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hinsA, hinsGood⟩
  have hc := hPmax (insert S P) hinsF
  simp [hSP] at hc

lemma exists_large_fiber {α β : Type} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (F : α → β) (m : ℕ)
    (h : m * (P.image F).card < P.card) :
    ∃ b ∈ P.image F, m < (P.filter fun a => F a = b).card := by
  classical
  by_contra! hle
  let B := P.image F
  let Q : β → Finset α := fun b => P.filter fun a => F a = b
  have hsub : P ⊆ B.biUnion Q := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨F a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  have hcard : P.card ≤ (B.biUnion Q).card := Finset.card_le_card hsub
  have hsum : (B.biUnion Q).card ≤ B.card * m := by
    calc
      (B.biUnion Q).card ≤ ∑ b ∈ B, (Q b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ B, m := Finset.sum_le_sum (fun b hb => hle b hb)
      _ = B.card * m := by simp [mul_comm]
  have : P.card ≤ m * (P.image F).card := by
    simpa [B, Q, mul_comm] using hcard.trans hsum
  omega

lemma exists_large_fiber' {α β : Type} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (F : α → β) (m : ℕ)
    (h : m * (P.image F).card < P.card) :
    ∃ b, m < (P.filter fun a => F a = b).card := by
  obtain ⟨b, _hb, hcard⟩ := exists_large_fiber P F m h
  exact ⟨b, hcard⟩

lemma pow_pred_mul {C : ℕ} (hC : 0 < C) : C * C ^ (C - 1) = C ^ C := by
  calc
    C * C ^ (C - 1) = C ^ (C - 1) * C := Nat.mul_comm _ _
    _ = C ^ ((C - 1) + 1) := (Nat.pow_succ C (C - 1)).symm
    _ = C ^ C := by congr 1; omega

lemma q_le_d {C : ℕ} (hC : 2 ≤ C) :
    (C + 1) * C ^ (C - 1) + C ≤ (2 * C) ^ C := by
  have hCs : C ≤ C ^ (C - 1) := Nat.le_pow (by omega)
  have h2 : 2 ≤ 2 ^ C := Nat.le_pow (by omega)
  have hp := pow_pred_mul (show 0 < C by omega)
  calc
    (C + 1) * C ^ (C - 1) + C ≤ (C + 1) * C ^ (C - 1) + C ^ (C - 1) :=
      Nat.add_le_add_left hCs _
    _ = (C + 2) * C ^ (C - 1) := by ring
    _ ≤ (2 * C) * C ^ (C - 1) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 * C ^ C := by rw [show (2 * C) * C ^ (C - 1) = 2 * (C * C ^ (C - 1)) by ring, hp]
    _ ≤ 2 ^ C * C ^ C := Nat.mul_le_mul_right _ h2
    _ = (2 * C) ^ C := (Nat.mul_pow 2 C C).symm

lemma amplified_size {C t : ℕ} (hC : 2 ≤ C) (ht : 1 ≤ t) :
    (C - 1) * C ^ t + C ≤ C ^ (t + 1) := by
  have hCt : C ≤ C ^ t := Nat.le_pow (by omega)
  calc
    (C - 1) * C ^ t + C ≤ (C - 1) * C ^ t + C ^ t := Nat.add_le_add_left hCt _
    _ = ((C - 1) + 1) * C ^ t := by ring
    _ = C * C ^ t := by rw [Nat.sub_add_cancel (by omega : 1 ≤ C)]
    _ = C ^ (t + 1) := by rw [Nat.pow_succ]; ring

lemma union_card_le {C t : ℕ} {ι : Type} [DecidableEq ι]
    (hC : 2 ≤ C) (ht : t ≤ C - 1) (P : Finset (Finset ι))
    (hP : P.card ≤ C * 2 ^ C) (hsz : ∀ S ∈ P, S.card ≤ C ^ t) :
    (P.biUnion (fun S => S)).card ≤ (2 * C) ^ C := by
  have hpow : C ^ t ≤ C ^ (C - 1) := Nat.pow_le_pow_right (by omega) ht
  have hp := pow_pred_mul (show 0 < C by omega)
  calc
    (P.biUnion (fun S => S)).card ≤ ∑ S ∈ P, S.card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ P, C ^ t := Finset.sum_le_sum hsz
    _ = P.card * C ^ t := by simp [mul_comm]
    _ ≤ (C * 2 ^ C) * C ^ t := Nat.mul_le_mul_right _ hP
    _ ≤ (C * 2 ^ C) * C ^ (C - 1) := Nat.mul_le_mul_left _ hpow
    _ = (2 * C) ^ C := by rw [Nat.mul_pow, ← hp]; ring

noncomputable def defAvoidingFamily {C : ℕ} (f : CoreColoring C) (t : ℕ) :
    Finset (Finset (Fin f.R)) := by
  classical
  exact Finset.univ.filter fun S => S.Nonempty ∧ S.card ≤ C ^ t ∧ AvoidsNumber f.color S t

lemma mem_avoidingFamily {C : ℕ} (f : CoreColoring C) (t : ℕ) (S : Finset (Fin f.R)) :
    S ∈ defAvoidingFamily f t ↔
      S.Nonempty ∧ S.card ≤ C ^ t ∧ AvoidsNumber f.color S t := by
  classical
  simp [defAvoidingFamily]

noncomputable def possibleTypes {C : ℕ} (f : CoreColoring C) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (C - 1)).filter fun t => (defAvoidingFamily f t).Nonempty

lemma initial_family {C : ℕ} (hC : 2 ≤ C) (f : CoreColoring C) :
    (defAvoidingFamily f 1).Nonempty := by
  obtain ⟨S, hSne, hScard, hSavoid⟩ :=
    (avoiding_amplification C (C ^ (C - 1)) f.R hC
      (Nat.one_le_pow _ _ (by omega)) f.positive f.W f.core_subset f.color f.admissible).1
  refine ⟨S, (mem_avoidingFamily f 1 S).mpr ?_⟩
  simpa using And.intro hSne (And.intro hScard hSavoid)

lemma possibleTypes_nonempty {C : ℕ} (hC : 2 ≤ C) (f : CoreColoring C) :
    (possibleTypes f).Nonempty := by
  classical
  refine ⟨1, Finset.mem_filter.mpr ⟨?_, initial_family hC f⟩⟩
  exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩

noncomputable def rawType {C : ℕ} (f : CoreColoring C) : ℕ := by
  classical
  exact if f.R ≤ (C + 1) * C ^ (C - 1) + C then 0
    else if h : (possibleTypes f).Nonempty then (possibleTypes f).max' h else 0

lemma rawType_mem {C : ℕ} (hC : 2 ≤ C) (f : CoreColoring C)
    (hlarge : ¬ f.R ≤ (C + 1) * C ^ (C - 1) + C) :
    rawType f ∈ possibleTypes f := by
  classical
  rw [rawType, if_neg hlarge, dif_pos (possibleTypes_nonempty hC f)]
  exact Finset.max'_mem _ _

lemma rawType_bounds {C : ℕ} (hC : 2 ≤ C) (f : CoreColoring C)
    (hlarge : ¬ f.R ≤ (C + 1) * C ^ (C - 1) + C) :
    1 ≤ rawType f ∧ rawType f ≤ C - 1 ∧ (defAvoidingFamily f (rawType f)).Nonempty := by
  classical
  have hm := Finset.mem_filter.mp (rawType_mem hC f hlarge)
  exact ⟨(Finset.mem_Icc.mp hm.1).1, (Finset.mem_Icc.mp hm.1).2, hm.2⟩

lemma rawType_maximal {C : ℕ} (hC : 2 ≤ C) (f : CoreColoring C)
    (hlarge : ¬ f.R ≤ (C + 1) * C ^ (C - 1) + C)
    (ht : rawType f < C - 1) : ¬ (defAvoidingFamily f (rawType f + 1)).Nonempty := by
  classical
  intro hnext
  have hmem : rawType f + 1 ∈ possibleTypes f := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hnext⟩
  have hle0 := Finset.le_max' (possibleTypes f) (rawType f + 1) hmem
  have hle : rawType f + 1 ≤ rawType f := by
    simpa [rawType, hlarge, possibleTypes_nonempty hC f] using hle0
  omega

noncomputable def maximalFamily {C : ℕ} (f : CoreColoring C) (t : ℕ) :
    Finset (Finset (Fin f.R)) :=
  Classical.choose (exists_maximal_disjoint_subfamily (defAvoidingFamily f t)
    (fun S hS => ((mem_avoidingFamily f t S).mp hS).1))

lemma maximalFamily_spec {C : ℕ} (f : CoreColoring C) (t : ℕ) :
    maximalFamily f t ⊆ defAvoidingFamily f t ∧
    (∀ S ∈ maximalFamily f t, ∀ U ∈ maximalFamily f t, S ≠ U → Disjoint S U) ∧
    ∀ S ∈ defAvoidingFamily f t,
      (S ∩ (maximalFamily f t).biUnion (fun U => U)).Nonempty := by
  exact Classical.choose_spec (exists_maximal_disjoint_subfamily (defAvoidingFamily f t)
    (fun S hS => ((mem_avoidingFamily f t S).mp hS).1))

lemma maximalFamily_nonempty {C : ℕ} (f : CoreColoring C) (t : ℕ)
    (hA : (defAvoidingFamily f t).Nonempty) : (maximalFamily f t).Nonempty := by
  obtain ⟨S, hS⟩ := hA
  have hi := (maximalFamily_spec f t).2.2 S hS
  obtain ⟨a, ha⟩ := hi.mono Finset.inter_subset_right
  obtain ⟨U, hU, _haU⟩ := Finset.mem_biUnion.mp ha
  exact ⟨U, hU⟩

noncomputable def selector {C : ℕ} (f : CoreColoring C) : Finset (Fin f.R) := by
  classical
  exact if f.R ≤ (C + 1) * C ^ (C - 1) + C then Finset.univ
    else (maximalFamily f (rawType f)).biUnion (fun S => S)

noncomputable def colorType {C : ℕ} (hC : 2 ≤ C) (f : CoreColoring C) : Fin C :=
  ⟨rawType f, by
    by_cases h : f.R ≤ (C + 1) * C ^ (C - 1) + C
    · rw [rawType, if_pos h]
      omega
    · have hb := rawType_bounds hC f h
      omega⟩

noncomputable def certificate {C : ℕ} (f : CoreColoring C) (t : ℕ)
    (S : Finset (Fin f.R)) : Finset (Fin C) := by
  classical
  exact if h : AvoidsNumber f.color S t then Classical.choose h else ∅

lemma certificate_spec {C : ℕ} (f : CoreColoring C) (t : ℕ) (S : Finset (Fin f.R))
    (h : AvoidsNumber f.color S t) :
    (certificate f t S).card = t ∧ Avoids f.color S (certificate f t S) := by
  classical
  rw [certificate, dif_pos h]
  exact Classical.choose_spec h

lemma maximalFamily_card {C : ℕ} (hC : 2 ≤ C) (f : CoreColoring C)
    (hlarge : ¬ f.R ≤ (C + 1) * C ^ (C - 1) + C) :
    (maximalFamily f (rawType f)).card ≤ C * 2 ^ C := by
  classical
  let t := rawType f
  let P := maximalFamily f t
  change P.card ≤ C * 2 ^ C
  by_contra hP
  have hPlt : C * 2 ^ C < P.card := Nat.lt_of_not_ge hP
  let B := P.image (certificate f t)
  have hB : B.card ≤ 2 ^ C := by
    calc
      B.card ≤ Fintype.card (Finset (Fin C)) := Finset.card_le_univ B
      _ = 2 ^ C := by simp
  have hex : ∃ T, C < (P.filter fun S => certificate f t S = T).card := by
    apply exists_large_fiber' P (certificate f t) C
    change C * B.card < P.card
    exact (Nat.mul_le_mul_left C hB).trans_lt hPlt
  obtain ⟨T, hT⟩ := hex
  let Q := P.filter fun S => certificate f t S = T
  have hTQ : C < Q.card := by simpa [Q] using hT
  have hQC : C + 1 ≤ Q.card := by omega
  obtain ⟨Q', hQ'Q, hQ'card⟩ := Finset.exists_subset_card_eq hQC
  let e := Q'.equivFin
  let S : Fin (C + 1) → Finset (Fin f.R) := fun i =>
    (e.symm (Fin.cast hQ'card.symm i)).val
  have hSQ' : ∀ i, S i ∈ Q' := by
    intro i
    exact (e.symm (Fin.cast hQ'card.symm i)).property
  have hSQ : ∀ i, S i ∈ Q := fun i => hQ'Q (hSQ' i)
  have hSP : ∀ i, S i ∈ P := fun i => (Finset.mem_filter.mp (hSQ i)).1
  have hScert : ∀ i, certificate f t (S i) = T := by
    intro i
    exact (Finset.mem_filter.mp (hSQ i)).2
  have hSinj : Function.Injective S := by
    intro i j hij
    have heq : e.symm (Fin.cast hQ'card.symm i) = e.symm (Fin.cast hQ'card.symm j) :=
      Subtype.ext hij
    have hfin := e.symm.injective heq
    apply Fin.ext
    have hv := congrArg Fin.val hfin
    simpa using hv
  have hSdis : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    exact (maximalFamily_spec f t).2.1 (S i) (hSP i) (S j) (hSP j)
      (fun heq => hij (hSinj heq))
  have hSA : ∀ i, S i ∈ defAvoidingFamily f t := fun i =>
    (maximalFamily_spec f t).1 (hSP i)
  have hSdata : ∀ i, (S i).Nonempty ∧ (S i).card ≤ C ^ t ∧ AvoidsNumber f.color (S i) t := by
    intro i
    exact (mem_avoidingFamily f t (S i)).mp (hSA i)
  have hTcard : T.card = t := by
    have hs := certificate_spec f t (S 0) (hSdata 0).2.2
    rw [hScert 0] at hs
    exact hs.1
  have hTavoid : ∀ i, Avoids f.color (S i) T := by
    intro i
    have hs := certificate_spec f t (S i) (hSdata i).2.2
    rw [hScert i] at hs
    exact hs.2
  have htbound := rawType_bounds hC f hlarge
  have hts : C ^ t ≤ C ^ (C - 1) := Nat.pow_le_pow_right (by omega) htbound.2.1
  have hcore : Core C (C ^ t) f.R ⊆ f.W := (core_mono hts).trans f.core_subset
  obtain ⟨b, U, hb, hUcard, hUavoid⟩ :=
    (avoiding_amplification C (C ^ t) f.R hC
      (Nat.one_le_pow _ _ (by omega)) f.positive f.W hcore f.color f.admissible).2
      T S (by omega) hSdis (fun i => ⟨(hSdata i).2.1, hTavoid i⟩)
  by_cases htlast : t = C - 1
  · have hFull : insert b T = Finset.univ := by
      apply Finset.eq_univ_of_card (insert b T)
      rw [Finset.card_insert_of_notMem hb, hTcard, htlast]
      simp only [Fintype.card_fin]
      omega
    have hWuniv : (Finset.univ : Finset (Fin f.R)) ∈ f.W := (core_testDomain f).2
    have hnot := hUavoid ⟨Finset.univ, hWuniv⟩ (by simp)
    rw [hFull] at hnot
    exact hnot (Finset.mem_univ _)
  · have htlt : t < C - 1 := by omega
    have hnext := rawType_maximal hC f hlarge htlt
    let a : Fin f.R := ⟨0, f.positive⟩
    let U' : Finset (Fin f.R) := if U.Nonempty then U else {a}
    have hU'ne : U'.Nonempty := by
      by_cases hU : U.Nonempty
      · simpa [U', hU] using hU
      · simp [U', hU]
    have hU'avoid : Avoids f.color U' (insert b T) := by
      by_cases hU : U.Nonempty
      · simpa [U', hU] using hUavoid
      · intro X _hX
        apply hUavoid X
        have hUe : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
        simp [hUe]
    have hU'card : U'.card ≤ C ^ (t + 1) := by
      by_cases hU : U.Nonempty
      · have hbound : U'.card ≤ (C - 1) * C ^ t + C := by
          simpa [U', hU] using hUcard
        exact hbound.trans (amplified_size hC htbound.1)
      · have hone : 1 ≤ C ^ (t + 1) := Nat.one_le_pow _ _ (by omega)
        simpa [U', hU] using hone
    have hU'number : AvoidsNumber f.color U' (t + 1) := by
      refine ⟨insert b T, ?_, hU'avoid⟩
      rw [Finset.card_insert_of_notMem hb, hTcard]
    apply hnext
    exact ⟨U', (mem_avoidingFamily f (t + 1) U').mpr ⟨hU'ne, hU'card, hU'number⟩⟩

lemma selector_nonempty_card {C : ℕ} (hC : 2 ≤ C) (f : CoreColoring C) :
    (selector f).Nonempty ∧ (selector f).card ≤ (2 * C) ^ C := by
  classical
  by_cases hsmall : f.R ≤ (C + 1) * C ^ (C - 1) + C
  · constructor
    · simp only [selector, hsmall, ↓reduceIte]
      exact ⟨⟨0, f.positive⟩, Finset.mem_univ _⟩
    · simpa [selector, hsmall] using hsmall.trans (q_le_d hC)
  · have hb := rawType_bounds hC f hsmall
    have hP := maximalFamily_nonempty f (rawType f) hb.2.2
    obtain ⟨S, hS⟩ := hP
    have hSne : S.Nonempty := ((mem_avoidingFamily f _ S).mp
      ((maximalFamily_spec f _).1 hS)).1
    have hUne : ((maximalFamily f (rawType f)).biUnion (fun U => U)).Nonempty :=
      hSne.mono (fun _ ha => Finset.mem_biUnion.mpr ⟨S, hS, ha⟩)
    constructor
    · simpa [selector, hsmall] using hUne
    · simp only [selector, hsmall, ↓reduceIte]
      exact union_card_le hC hb.2.1 _ (maximalFamily_card hC f hsmall)
        (fun U hU => ((mem_avoidingFamily f _ U).mp
          ((maximalFamily_spec f _).1 hU)).2.1)

lemma selector_compatible {C : ℕ} (hC : 2 ≤ C) (f g : CoreColoring C)
    (π : Fin f.R → Fin g.R) (hminor : ExactMinor f.color g.color π)
    (htype : colorType hC f = colorType hC g) :
    ((selector f).image π ∩ selector g).Nonempty := by
  classical
  have hval : rawType f = rawType g := congrArg Fin.val htype
  by_cases hf : f.R ≤ (C + 1) * C ^ (C - 1) + C
  · have hg : g.R ≤ (C + 1) * C ^ (C - 1) + C := by
      by_contra hg
      have hb := rawType_bounds hC g hg
      have hf0 : rawType f = 0 := by rw [rawType, if_pos hf]
      omega
    let a : Fin f.R := ⟨0, f.positive⟩
    refine ⟨π a, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨a, by simp [selector, hf], rfl⟩
    · simp [selector, hg]
  · have hg : ¬ g.R ≤ (C + 1) * C ^ (C - 1) + C := by
      intro hg
      have hb := rawType_bounds hC f hf
      have hg0 : rawType g = 0 := by rw [rawType, if_pos hg]
      omega
    have hbf := rawType_bounds hC f hf
    obtain ⟨S, hSP⟩ := maximalFamily_nonempty f (rawType f) hbf.2.2
    have hSdata := (mem_avoidingFamily f (rawType f) S).mp
      ((maximalFamily_spec f (rawType f)).1 hSP)
    obtain ⟨T, hTcard, hTavoid⟩ := hSdata.2.2
    have himageAvoid : Avoids g.color (S.image π) T :=
      avoiding_minor f.positive g.positive hC (core_testDomain f) (core_testDomain g)
        f.color g.color π hminor S T hTavoid
    have himageA : S.image π ∈ defAvoidingFamily g (rawType g) := by
      apply (mem_avoidingFamily g (rawType g) (S.image π)).mpr
      refine ⟨hSdata.1.image π, Finset.card_image_le.trans ?_, T, ?_, himageAvoid⟩
      · simpa [← hval] using hSdata.2.1
      · simpa [← hval] using hTcard
    have hi := (maximalFamily_spec g (rawType g)).2.2 (S.image π) himageA
    simp only [selector, hf, hg, ↓reduceIte]
    obtain ⟨a, ha⟩ := hi
    have ha' := Finset.mem_inter.mp ha
    refine ⟨a, Finset.mem_inter.mpr ⟨?_, ha'.2⟩⟩
    obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.mp ha'.1
    exact Finset.mem_image.mpr ⟨b, Finset.mem_biUnion.mpr ⟨S, hSP, hbS⟩, rfl⟩

end SelectorProof

open SelectorProof

theorem solution (C : ℕ) (hC : 2 ≤ C) :
    ∃ (τ : CoreColoring C → Fin C) (Sel : (f : CoreColoring C) → Finset (Fin f.R)),
      (∀ f, (Sel f).Nonempty ∧ (Sel f).card ≤ (2 * C) ^ C) ∧
      ∀ (f g : CoreColoring C) (π : Fin f.R → Fin g.R),
        ExactMinor f.color g.color π → τ f = τ g →
          ((Sel f).image π ∩ Sel g).Nonempty := by
  refine ⟨colorType hC, selector, selector_nonempty_card hC, ?_⟩
  intro f g π hminor htype
  exact selector_compatible hC f g π hminor htype
