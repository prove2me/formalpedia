-- Prove2me | solution 1 for BinaryThreeLCC.JM.padded_span_dimension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:05:29.528414+00:00
-- url     : https://prove2.me/submissions/5c7f5ab6-853c-4c25-915d-25e3a75ba7ea

import Definitions.Def_BinaryThreeLCC_Main_Matchings

set_option autoImplicit false

namespace BinaryThreeLCC.JM

open BinaryThreeLCC.Main

namespace T2aux

theorem zmod2_ne_zero (x : Bit) (h : x ≠ 0) : x = 1 := by
  revert x; decide

theorem zmod2_add_self (x : Bit) : x + x = 0 := by
  revert x; decide

theorem zmod2_add_one_eq (x o : Bit) : x + 1 = o ↔ x ≠ o := by
  revert x o; decide

theorem lin_expand {k : ℕ} {M : Type*} [AddCommGroup M] [Module Bit M]
    (f : (Fin k → Bit) →ₗ[Bit] M) (x : Fin k → Bit) :
    f x = ∑ j, x j • f (Pi.single j 1) := by
  conv_lhs => rw [show x = ∑ j, x j • (Pi.single j 1 : Fin k → Bit) by
    ext i; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, map_smul]

theorem enc_apply {k n : ℕ} (C : CodeModel k n) (b : Fin k → Bit) (u : Fin n) :
    C.encoding b u = ∑ j, b j * codeRow C u j := by
  rw [lin_expand C.encoding b]
  simp [Finset.sum_apply, codeRow, smul_eq_mul]

theorem dual_apply {k : ℕ} (f : Module.Dual Bit (Fin k → Bit)) (x : Fin k → Bit) :
    f x = ∑ j, x j * f (Pi.single j 1) := by
  rw [lin_expand f x]
  simp [smul_eq_mul]

/-- If a row avoids the span of finitely many rows, a message flips it while
fixing those rows. -/
theorem exists_flip {k n : ℕ} (C : CodeModel k n) (Q : Finset (Fin n)) (u : Fin n)
    (h : codeRow C u ∉ Submodule.span Bit (codeRow C '' (Q : Set (Fin n)))) :
    ∃ b0 : Fin k → Bit, (∀ q ∈ Q, C.encoding b0 q = 0) ∧ C.encoding b0 u = 1 := by
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  have key : ∀ q, C.encoding (fun j => f (Pi.single j 1)) q = f (codeRow C q) := by
    intro q
    rw [enc_apply, dual_apply f (codeRow C q)]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  refine ⟨fun j => f (Pi.single j 1), fun q hq => ?_, ?_⟩
  · rw [key]
    have : f (codeRow C q) ∈ (Submodule.span Bit (codeRow C '' (Q : Set (Fin n)))).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨q, hq, rfl⟩)
    rw [hf2] at this
    simpa using this
  · rw [key]; exact zmod2_ne_zero _ hf1

theorem span_padded_top {k n : ℕ} (C : CodeModel k n) :
    Submodule.span Bit (Set.range (paddedRow C)) = ⊤ := by
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, x ∉ Submodule.span Bit (Set.range (paddedRow C)) := by
    by_contra hall
    push Not at hall
    exact hne (Submodule.eq_top_iff'.2 hall)
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  set b : Fin k → Bit := fun j => f (Pi.single j 1) with hb
  have hzero : C.encoding b = 0 := by
    ext q
    rw [enc_apply]
    have hq : codeRow C q = paddedRow C ⟨q.val, by omega⟩ := by
      simp [paddedRow]
    have hmem : f (codeRow C q) ∈ (Submodule.span Bit (Set.range (paddedRow C))).map f := by
      rw [hq]; exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, rfl⟩)
    rw [hf2] at hmem
    have h0 : f (codeRow C q) = 0 := by simpa using hmem
    rw [dual_apply f] at h0
    simp only [Pi.zero_apply]
    rw [← h0]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hb0 : b = 0 := C.injective (by rw [hzero, map_zero])
  apply hf1
  rw [dual_apply f x]
  have : ∀ j, f (Pi.single j 1) = 0 := fun j => by
    have := congrFun hb0 j
    simpa [hb] using this
  simp [this]

theorem half_count {k n : ℕ} (C : CodeModel k n) (u : Fin n)
    (A : Finset (Fin k → Bit)) (b0 : Fin k → Bit) (hA : ∀ b ∈ A, b + b0 ∈ A)
    (hb0 : C.encoding b0 u = 1) (o : Bit) :
    2 * (A.filter (fun b => o = C.encoding b u)).card = A.card := by
  have hinv : ∀ b : Fin k → Bit, b + b0 + b0 = b := by
    intro b; ext j; simp [add_assoc, zmod2_add_self]
  have hsame : (A.filter (fun b => o = C.encoding b u)).card =
      (A.filter (fun b => ¬ (o = C.encoding b u))).card := by
    apply Finset.card_nbij' (· + b0) (· + b0)
    · intro b hb
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨hA b hb.1, ?_⟩
      rw [map_add, Pi.add_apply, hb0, ← hb.2]
      intro h
      have := (zmod2_add_one_eq o o).1 h.symm
      exact this rfl
    · intro b hb
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨hA b hb.1, ?_⟩
      rw [map_add, Pi.add_apply, hb0]
      exact ((zmod2_add_one_eq _ o).2 (fun h => hb.2 h.symm)).symm
    · intro b _; exact hinv b
    · intro b _; exact hinv b
  have := Finset.card_filter_add_card_filter_not (s := A)
    (fun b => o = C.encoding b u)
  omega

theorem split_card {k : ℕ} (p : (Fin k → Bit) → Prop) [DecidablePred p]
    (L : (Fin k → Bit) → Bit) :
    (Finset.univ.filter p).card = (Finset.univ.filter (fun b => p b ∧ L b = 0)).card +
      (Finset.univ.filter (fun b => p b ∧ L b = 1)).card := by
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter p) (fun b => L b = 0),
    Finset.filter_filter, Finset.filter_filter]
  congr 2
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, zmod2_ne_zero _ h2⟩
  · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rw [h2]; decide

/-- The received word: zero on the corrupted set `Z`, the codeword elsewhere. -/
def yv {k n : ℕ} (C : CodeModel k n) (Z : Finset (Fin n)) (b : Fin k → Bit) :
    Fin n → Bit := fun i => if i ∈ Z then 0 else C.encoding b i

theorem cons_insert {k n : ℕ} (C : CodeModel k n) (P : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ P) (c : Fin n → Bit) (β : Bit) (b : Fin k → Bit) :
    (∀ q ∈ insert i P, C.encoding b q = Function.update c i β q) ↔
      (∀ q ∈ P, C.encoding b q = c q) ∧ C.encoding b i = β := by
  constructor
  · intro h
    refine ⟨fun q hq => ?_, ?_⟩
    · have := h q (Finset.mem_insert_of_mem hq)
      rwa [Function.update_of_ne (by rintro rfl; exact hi hq)] at this
    · have := h i (Finset.mem_insert_self i P)
      rwa [Function.update_self] at this
  · rintro ⟨h1, h2⟩ q hq
    rcases Finset.mem_insert.1 hq with rfl | hq'
    · rw [Function.update_self]; exact h2
    · rw [Function.update_of_ne (by rintro rfl; exact hi hq')]; exact h1 q hq'

theorem card_filter_congr' {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] (h : ∀ x, p x ↔ q x) :
    (Finset.univ.filter p).card = (Finset.univ.filter q).card := by
  congr 1; exact Finset.filter_congr (fun x _ => h x)

theorem tree_count {k n : ℕ} (C : CodeModel k n) (u : Fin n) (Z : Finset (Fin n))
    (hAv : ∀ Q : Finset (Fin n), Disjoint Q Z → Q.card ≤ 3 →
      codeRow C u ∉ Submodule.span Bit (codeRow C '' (Q : Set (Fin n)))) :
    ∀ (t : MantriCVQ.DT n) (P : Finset (Fin n)), Disjoint P Z → P.card + t.depth ≤ 3 →
      ∀ c : Fin n → Bit,
      2 * (Finset.univ.filter (fun b : Fin k → Bit => (∀ q ∈ P, C.encoding b q = c q) ∧
        (if t.eval (fun i => yv C Z b i == 1) then (1 : Bit) else 0) = C.encoding b u)).card =
      (Finset.univ.filter (fun b : Fin k → Bit => ∀ q ∈ P, C.encoding b q = c q)).card := by
  intro t
  induction t with
  | leaf β =>
    intro P hP hcard c
    obtain ⟨b0, hb0P, hb0u⟩ := exists_flip C P u
      (hAv P hP (by simp [MantriCVQ.DT.depth] at hcard; omega))
    have hcl : ∀ b ∈ Finset.univ.filter (fun b : Fin k → Bit => ∀ q ∈ P, C.encoding b q = c q),
        b + b0 ∈ Finset.univ.filter (fun b : Fin k → Bit => ∀ q ∈ P, C.encoding b q = c q) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      intro q hq
      rw [map_add, Pi.add_apply, hb q hq, hb0P q hq, add_zero]
    rw [← half_count C u _ b0 hcl hb0u (if β then 1 else 0), Finset.filter_filter]
    rfl
  | query i t0 t1 ih0 ih1 =>
    intro P hP hcard c
    have hd0 : P.card + t0.depth ≤ 3 := by
      have := le_max_left t0.depth t1.depth
      simp only [MantriCVQ.DT.depth] at hcard; omega
    have hd1 : P.card + t1.depth ≤ 3 := by
      have := le_max_right t0.depth t1.depth
      simp only [MantriCVQ.DT.depth] at hcard; omega
    by_cases hiZ : i ∈ Z
    · have hy : ∀ b, (yv C Z b i == 1) = false := by
        intro b; simp only [yv, hiZ, if_true]; decide
      rw [← ih0 P hP hd0 c]
      congr 1
      apply card_filter_congr'
      intro b
      simp only [MantriCVQ.DT.eval, hy b, Bool.false_eq_true, if_false]
    · have hyb : ∀ b, yv C Z b i = C.encoding b i := by
        intro b; simp only [yv, hiZ, if_false]
      by_cases hiP : i ∈ P
      · cases hci : (c i == 1)
        · rw [← ih0 P hP hd0 c]
          congr 1
          apply card_filter_congr'
          intro b
          simp only [MantriCVQ.DT.eval]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨h1, ?_⟩
            simpa [hyb b, h1 i hiP, hci] using h2
          · rintro ⟨h1, h2⟩
            refine ⟨h1, ?_⟩
            simpa [hyb b, h1 i hiP, hci] using h2
        · rw [← ih1 P hP hd1 c]
          congr 1
          apply card_filter_congr'
          intro b
          simp only [MantriCVQ.DT.eval]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨h1, ?_⟩
            simpa [hyb b, h1 i hiP, hci] using h2
          · rintro ⟨h1, h2⟩
            refine ⟨h1, ?_⟩
            simpa [hyb b, h1 i hiP, hci] using h2
      · have hP' : Disjoint (insert i P) Z := Finset.disjoint_insert_left.2 ⟨hiZ, hP⟩
        have hc0 : (insert i P).card + t0.depth ≤ 3 := by
          rw [Finset.card_insert_of_notMem hiP]
          have := le_max_left t0.depth t1.depth
          simp only [MantriCVQ.DT.depth] at hcard; omega
        have hc1 : (insert i P).card + t1.depth ≤ 3 := by
          rw [Finset.card_insert_of_notMem hiP]
          have := le_max_right t0.depth t1.depth
          simp only [MantriCVQ.DT.depth] at hcard; omega
        have e0 := ih0 (insert i P) hP' hc0 (Function.update c i 0)
        have e1 := ih1 (insert i P) hP' hc1 (Function.update c i 1)
        simp only [cons_insert C P i hiP] at e0 e1
        rw [split_card _ (fun b => C.encoding b i),
          split_card (fun b : Fin k → Bit => ∀ q ∈ P, C.encoding b q = c q)
            (fun b => C.encoding b i), ← e0, ← e1, mul_add]
        have h01 : ((0 : Bit) == 1) = false := by decide
        have h11 : ((1 : Bit) == 1) = true := by decide
        congr 2
        · apply card_filter_congr'
          intro b
          simp only [MantriCVQ.DT.eval]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            refine ⟨⟨h1, h3⟩, ?_⟩
            simpa [hyb b, h3, h01] using h2
          · rintro ⟨⟨h1, h3⟩, h2⟩
            refine ⟨⟨h1, ?_⟩, h3⟩
            simpa [hyb b, h3, h01] using h2
        · apply card_filter_congr'
          intro b
          simp only [MantriCVQ.DT.eval]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            refine ⟨⟨h1, h3⟩, ?_⟩
            simpa [hyb b, h3, h11] using h2
          · rintro ⟨⟨h1, h3⟩, h2⟩
            refine ⟨⟨h1, ?_⟩, h3⟩
            simpa [hyb b, h3, h11] using h2

theorem card_msgs (k : ℕ) : Fintype.card (Fin k → Bit) = 2 ^ k := by
  simp [Fintype.card_fun, ZMod.card]

/-- The core contradiction: a corruption set within the radius that hides the target row from
every set of at most three uncorrupted rows defeats the corrector. -/
theorem core {k n : ℕ} (C : CodeModel k n) (δ ε : ℝ) (hε1 : ε < 1 / 2)
    (hcorrect : Corrects C δ ε) (u : Fin n) (Z : Finset (Fin n))
    (hZ : (Z.card : ℝ) ≤ δ * n)
    (hAv : ∀ Q : Finset (Fin n), Disjoint Q Z → Q.card ≤ 3 →
      codeRow C u ∉ Submodule.span Bit (codeRow C '' (Q : Set (Fin n)))) : False := by
  classical
  have hcount : ∀ t : QueryTree n 3,
      2 * (Finset.univ.filter
        (fun b : Fin k → Bit => runTree t (yv C Z b) = C.encoding b u)).card = 2 ^ k := by
    intro t
    have h := tree_count C u Z hAv t.val ∅ (Finset.disjoint_empty_left _)
      (by simpa using t.property) (fun _ => 0)
    rw [card_filter_congr' _ (fun b : Fin k → Bit => (∀ q ∈ (∅ : Finset (Fin n)),
        C.encoding b q = (fun _ => (0 : Bit)) q) ∧
        (if t.val.eval (fun i => yv C Z b i == 1) then (1 : Bit) else 0) = C.encoding b u)
        (fun b => by simp [runTree]), h]
    rw [← card_msgs k, ← Finset.card_univ]
    congr 1
    apply Finset.filter_true_of_mem
    intro b _ q hq
    simp at hq
  have hdist : ∀ b : Fin k → Bit, (hamming (yv C Z b) (C.encoding b) : ℝ) ≤ δ * n := by
    intro b
    refine le_trans ?_ hZ
    unfold hamming
    exact_mod_cast Finset.card_le_card (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hiZ
      exact hi (by simp [yv, hiZ]))
  have hsucc : ∀ b : Fin k → Bit,
      1 - ε ≤ successProbability C (yv C Z b) u (C.encoding b u) :=
    fun b => hcorrect b (yv C Z b) u (hdist b)
  set p := C.decoder u with hp
  have hE : ∑ b : Fin k → Bit, p.toOuterMeasure
      {t | runTree t (yv C Z b) = C.encoding b u} = 2 ^ k / 2 := by
    simp only [PMF.toOuterMeasure_apply]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    have : ∀ t : QueryTree n 3, ∑ b : Fin k → Bit,
        Set.indicator {t | runTree t (yv C Z b) = C.encoding b u} p t = p t * (2 ^ k / 2) := by
      intro t
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      congr 1
      rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]
      have h := hcount t
      have h' : (((2 * (Finset.univ.filter
          (fun b : Fin k → Bit => runTree t (yv C Z b) = C.encoding b u)).card : ℕ)) : ENNReal) =
          ((2 ^ k : ℕ) : ENNReal) := by rw [h]
      push_cast at h'
      convert h' using 3
    simp only [this]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hR : ∑ b : Fin k → Bit, successProbability C (yv C Z b) u (C.encoding b u) =
      2 ^ k / 2 := by
    unfold successProbability
    rw [← hp, ← ENNReal.toReal_sum (fun b _ => by
      rw [PMF.toOuterMeasure_apply]; exact p.tsum_coe_indicator_ne_top _), hE]
    rw [ENNReal.toReal_div, ENNReal.toReal_pow]
    norm_num
  have hlow : ∑ b : Fin k → Bit, (1 - ε) ≤ 2 ^ k / 2 := by
    rw [← hR]; exact Finset.sum_le_sum (fun b _ => hsucc b)
  rw [Finset.sum_const, Finset.card_univ, card_msgs, nsmul_eq_mul] at hlow
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  push_cast at hlow
  nlinarith

end T2aux

end BinaryThreeLCC.JM

open BinaryThreeLCC.JM BinaryThreeLCC.JM.T2aux BinaryThreeLCC.Main

open T2aux in
/-- T1: the padded rows of an injective linear code span the whole message dual. -/
theorem solution {k n : ℕ} (C : CodeModel k n) :
    spanDimension (paddedRow C) = k := by
  unfold spanDimension
  rw [span_padded_top C, finrank_top, Module.finrank_fin_fun]


namespace BinaryThreeLCC.JM

open T2aux in
/-- T2: Fact 2.1 (one target, nonzero row). -/
theorem recovery_matching_of_corrects {k n : ℕ} (C : CodeModel k n) (δ ε : ℝ)
    (hε1 : ε < 1 / 2) (hcorrect : Corrects C δ ε) (u : Fin n) (hu : codeRow C u ≠ 0) :
    ∃ H : Finset (Finset (Fin (2 * n))),
      IsRecoveryMatching (⟨u.val, by omega⟩ : Fin (2 * n)) H ∧
      δ * n < 3 * (H.card : ℝ) + 1 ∧
      ∀ e ∈ H, paddedRow C ⟨u.val, by omega⟩ = ∑ a ∈ e, paddedRow C a := by
  classical
  set u' : Fin (2 * n) := ⟨u.val, by omega⟩ with hu'
  let emb : Fin n ↪ Fin (2 * n) := ⟨fun i => ⟨i.val, by omega⟩, fun a b h => by
    simpa [Fin.ext_iff] using h⟩
  have hemb : ∀ i : Fin n, (emb i).val = i.val := fun i => rfl
  let valid : Finset (Finset (Fin (2 * n))) → Prop := fun H =>
    IsRecoveryMatching u' H ∧ ∀ e ∈ H, paddedRow C u' = ∑ a ∈ e, paddedRow C a
  obtain ⟨H, hHmem, hHmax⟩ := Finset.exists_max_image (Finset.univ.filter valid) Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [valid, IsRecoveryMatching]⟩⟩
  have hHv : valid H := (Finset.mem_filter.1 hHmem).2
  refine ⟨H, hHv.1, ?_, hHv.2⟩
  by_contra hlt
  push Not at hlt
  set S := H.biUnion id with hSdef
  have hS : S.card ≤ 3 * H.card := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ a ∈ H, (id a).card ≤ ∑ _a ∈ H, 3 :=
          Finset.sum_le_sum (fun a ha => (hHv.1.1 a ha).1.le)
      _ = 3 * H.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hSr : (S.card : ℝ) ≤ 3 * H.card := by exact_mod_cast hS
  have hrow : ∀ q : Fin n, paddedRow C (emb q) = codeRow C q := by
    intro q; unfold paddedRow; rw [dif_pos (show (emb q).val < n from q.isLt)]; rfl
  have hu_row : paddedRow C u' = codeRow C u := hrow u
  by_cases hbig : 3 * H.card + 2 ≤ n
  · set Z : Finset (Fin n) := insert u (Finset.univ.filter (fun i => emb i ∈ S)) with hZdef
    apply core C δ ε hε1 hcorrect u Z
    · have h1 : (Finset.univ.filter (fun i => emb i ∈ S)).card ≤ S.card :=
        Finset.card_le_card_of_injOn emb (fun i hi => by simpa using hi)
          (fun a _ b _ h => emb.injective h)
      have h2 := Finset.card_insert_le u (Finset.univ.filter (fun i => emb i ∈ S))
      have : (Z.card : ℝ) ≤ S.card + 1 := by exact_mod_cast (h2.trans (by omega))
      linarith
    · intro Q hQZ hQ3 hmem
      obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' Bit).1 hmem
      set Q2 := Q.filter (fun q => c q = 1) with hQ2
      have hsumQ : ∑ q ∈ Q2, codeRow C q = codeRow C u := by
        rw [← hc, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        by_cases hcq : c q = 1
        · simp [hcq]
        · have : c q = 0 := by
            by_contra h0; exact hcq (zmod2_ne_zero _ h0)
          simp [hcq, this]
      have hQ2ne : Q2.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.sum_empty] at hsumQ
        exact hu hsumQ.symm
      have hQ2sub : Q2 ⊆ Q := Finset.filter_subset _ _
      set E0 := Q2.map emb with hE0
      have hE0card : E0.card = Q2.card := Finset.card_map _
      have hE0le : E0.card ≤ 3 := by rw [hE0card]; exact (Finset.card_le_card hQ2sub).trans hQ3
      have hE0pos : 1 ≤ E0.card := by rw [hE0card]; exact hQ2ne.card_pos
      set Pad := Finset.univ.filter (fun j : Fin (2 * n) => n ≤ j.val ∧ j ∉ S) with hPad
      have hPadcard : 2 ≤ Pad.card := by
        let sh : Fin n → Fin (2 * n) := fun j => ⟨n + j.val, by omega⟩
        have hall : n ≤ (Finset.univ.filter (fun j : Fin (2 * n) => n ≤ j.val)).card := by
          have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin n)))
            (t := Finset.univ.filter (fun j : Fin (2 * n) => n ≤ j.val)) sh
            (fun i _ => by simp [sh])
            (fun a _ b _ h => by
              simp only [sh, Fin.ext_iff] at h; exact Fin.ext (by omega))
          simpa using this
        have hsub : Finset.univ.filter (fun j : Fin (2 * n) => n ≤ j.val) ⊆ Pad ∪ S := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          by_cases hjS : j ∈ S
          · exact Finset.mem_union_right _ hjS
          · exact Finset.mem_union_left _ (by simp [hPad, hj, hjS])
        have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        omega
      obtain ⟨Pz, hPzsub, hPzcard⟩ :=
        Finset.exists_subset_card_eq (s := Pad) (n := 3 - E0.card) (by omega)
      have hE0val : ∀ a ∈ E0, a.val < n := by
        intro a ha
        obtain ⟨q, _, rfl⟩ := Finset.mem_map.1 ha
        rw [hemb]; exact q.isLt
      have hPzval : ∀ a ∈ Pz, n ≤ a.val ∧ a ∉ S := by
        intro a ha
        have := hPzsub ha
        simp only [hPad, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this
      have hdisj : Disjoint E0 Pz := by
        rw [Finset.disjoint_left]
        intro a ha hb
        have := hE0val a ha
        have := (hPzval a hb).1
        omega
      set e := E0 ∪ Pz with he
      have hecard : e.card = 3 := by
        rw [Finset.card_union_of_disjoint hdisj, hPzcard]; omega
      have heS : ∀ a ∈ e, a ∉ S := by
        intro a ha
        rcases Finset.mem_union.1 ha with ha | ha
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 ha
          intro hqS
          have hqZ : q ∈ Z := Finset.mem_insert_of_mem (by simpa using hqS)
          exact Finset.disjoint_left.1 hQZ (hQ2sub hq) hqZ
        · exact (hPzval a ha).2
      have hue : u' ∉ e := by
        intro hmem'
        rcases Finset.mem_union.1 hmem' with ha | ha
        · obtain ⟨q, hq, hqu⟩ := Finset.mem_map.1 ha
          have : q = u := by
            apply Fin.ext
            have := congrArg Fin.val hqu
            rw [hemb] at this
            simpa [hu'] using this
          subst this
          exact Finset.disjoint_left.1 hQZ (hQ2sub hq) (Finset.mem_insert_self _ _)
        · have := (hPzval u' ha).1
          simp [hu'] at this
          omega
      have hesum : paddedRow C u' = ∑ a ∈ e, paddedRow C a := by
        rw [Finset.sum_union hdisj, Finset.sum_map]
        have h0 : ∑ a ∈ Pz, paddedRow C a = 0 := by
          refine Finset.sum_eq_zero (fun a ha => ?_)
          have := (hPzval a ha).1
          simp [paddedRow, show ¬ a.val < n by omega]
        rw [h0, add_zero, hu_row]
        simp_rw [hrow]
        exact hsumQ.symm
      have heH : e ∉ H := by
        intro heH
        have hsub : e ⊆ S := Finset.subset_biUnion_of_mem id heH
        have hne : e.Nonempty := Finset.card_pos.1 (by omega)
        obtain ⟨a, ha⟩ := hne
        exact heS a ha (hsub ha)
      have hvalid : valid (insert e H) := by
        refine ⟨⟨fun f hf => ?_, fun f hf g hg hfg => ?_⟩, fun f hf => ?_⟩
        · rcases Finset.mem_insert.1 hf with rfl | hf
          · exact ⟨hecard, hue⟩
          · exact hHv.1.1 f hf
        · have key : ∀ g ∈ H, Disjoint e g := by
            intro g hg
            rw [Finset.disjoint_left]
            intro a hae hag
            exact heS a hae (Finset.subset_biUnion_of_mem id hg hag)
          rcases Finset.mem_insert.1 hf with rfl | hf
          · rcases Finset.mem_insert.1 hg with rfl | hg
            · exact absurd rfl hfg
            · exact key g hg
          · rcases Finset.mem_insert.1 hg with rfl | hg
            · exact (key f hf).symm
            · exact hHv.1.2 f hf g hg hfg
        · rcases Finset.mem_insert.1 hf with rfl | hf
          · exact hesum
          · exact hHv.2 f hf
      have := hHmax (insert e H) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hvalid⟩)
      rw [Finset.card_insert_of_notMem heH] at this
      omega
  · apply core C δ ε hε1 hcorrect u Finset.univ
    · have : (n : ℝ) ≤ 3 * H.card + 1 := by
        have : n ≤ 3 * H.card + 1 := by omega
        exact_mod_cast this
      simp only [Finset.card_univ, Fintype.card_fin]
      linarith
    · intro Q hQZ _ hmem
      have hQ : Q = ∅ := Finset.eq_empty_of_forall_notMem
        (fun q hq => Finset.disjoint_left.1 hQZ hq (Finset.mem_univ q))
      subst hQ
      simp at hmem
      exact hu hmem

end BinaryThreeLCC.JM
