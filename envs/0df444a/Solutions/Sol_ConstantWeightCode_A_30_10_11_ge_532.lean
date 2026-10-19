-- Prove2me | solution 1 for ConstantWeightCode.A_30_10_11_ge_532
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T15:31:31.453545+00:00
-- url     : https://prove2.me/submissions/cbf2bdfd-c704-4c5e-99a9-967c051651f9

import Mathlib

set_option autoImplicit false

namespace CwA30

/-! ## Bit-sliced checker for binary constant-weight codes

A code of `M` words of length `n` is given twice: as the list `words` (word `j` is the Nat whose bit `c`
is coordinate `c`) and as the list `cols` of its `n` columns (column `c` is the `M`-bit Nat whose bit `j`
is coordinate `c` of word `j`); `cols` is checked to be the transpose of `words`.

For a word `x`, `run x 0 cols Ts` walks the columns in the support of `x` and maintains unary saturating
counters, one bit-slice per word: bit `j` of the `k`-th counter (0-based) says that word `j` meets the support
of `x` in at least `k + 1` coordinates.  Everything below is proved; the final check is `decide +kernel`. -/

/-- advance all counters by one column `B`; `p` is the previous (lower) counter. -/
def upd (B : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | p, t :: ts => (t ||| (p &&& B)) :: upd B t ts

/-- process the columns `cs` (the first one has index `c`), using only those in the support of `x`. -/
def run (x : ℕ) : ℕ → List ℕ → List ℕ → List ℕ
  | _, [], Ts => Ts
  | c, B :: cs, Ts => run x (c + 1) cs (if x.testBit c then upd B B Ts else Ts)

/-- column `c` of a list of words: bit `j` is bit `c` of word `j`. -/
def colOf : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: xs, c => Nat.bit (x.testBit c) (colOf xs c)

/-- row check: for every word `x = words[i]`, the counter "overlap ≥ s + 1" is exactly `{i}`. -/
def rowsOk (cols : List ℕ) (s : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, x :: xs => ((run x 0 cols (List.replicate (s + 1) 0)).getD s 0 == 2 ^ i) && rowsOk cols s (i + 1) xs

/-- weight check: every word has at least `w` and not `w + 1` ones among the `n` coordinates. -/
def weightOk (cols : List ℕ) (n M w : ℕ) : Bool :=
  ((run (2 ^ n - 1) 0 cols (List.replicate (w + 1) 0)).getD (w - 1) 0 == 2 ^ M - 1) &&
  ((run (2 ^ n - 1) 0 cols (List.replicate (w + 1) 0)).getD w 0 == 0)

/-- `Rep j m k Ts`: bit `j` of the `idx`-th entry of `Ts` is `decide (k + idx + 1 ≤ m)`. -/
def Rep (j m : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | k, t :: ts => t.testBit j = decide (k + 1 ≤ m) ∧ Rep j m (k + 1) ts

theorem upd_length (B : ℕ) : ∀ (Ts : List ℕ) (p : ℕ), (upd B p Ts).length = Ts.length := by
  intro Ts
  induction Ts with
  | nil => intro p; simp [upd]
  | cons t ts ih => intro p; simp [upd, ih]

theorem run_length (x : ℕ) : ∀ (cs : List ℕ) (c : ℕ) (Ts : List ℕ), (run x c cs Ts).length = Ts.length := by
  intro cs
  induction cs with
  | nil => intro c Ts; simp [run]
  | cons B cs ih =>
    intro c Ts
    simp only [run, ih]
    split <;> simp [upd_length]

theorem rep_replicate (j : ℕ) (K : ℕ) : ∀ k, Rep j 0 k (List.replicate K 0) := by
  induction K with
  | zero => intro k; simp [Rep]
  | succ K ih => intro k; simp only [List.replicate_succ, Rep]; exact ⟨by simp, ih (k + 1)⟩

theorem upd_rep (B j : ℕ) : ∀ (Ts : List ℕ) (k m p : ℕ), Rep j m k Ts →
    (p.testBit j && B.testBit j) = (decide (k ≤ m) && B.testBit j) →
    Rep j (m + if B.testBit j then 1 else 0) k (upd B p Ts) := by
  intro Ts
  induction Ts with
  | nil => intro k m p _ _; simp [upd, Rep]
  | cons t ts ih =>
    intro k m p h hp
    simp only [Rep] at h
    obtain ⟨ht, hts⟩ := h
    simp only [upd, Rep]
    refine ⟨?_, ih (k + 1) m t hts (by rw [ht])⟩
    rw [Nat.testBit_or, Nat.testBit_and, hp, ht]
    cases hB : B.testBit j
    · simp
    · by_cases h2 : k ≤ m
      · have h3 : k + 1 ≤ m + 1 := by omega
        simp [h2, h3]
      · have h1 : ¬ k + 1 ≤ m := by omega
        have h3 : ¬ k + 1 ≤ m + 1 := by omega
        simp [h1, h2, h3]

theorem run_rep (x j : ℕ) : ∀ (cs : List ℕ) (c m : ℕ) (Ts : List ℕ), Rep j m 0 Ts →
    Rep j (m + ∑ i ∈ Finset.range cs.length,
      if (x.testBit (c + i) && (cs.getD i 0).testBit j) then 1 else 0) 0 (run x c cs Ts) := by
  intro cs
  induction cs with
  | nil => intro c m Ts h; simpa [run] using h
  | cons B cs ih =>
    intro c m Ts h
    have h1 : Rep j (m + if (x.testBit c && B.testBit j) then 1 else 0) 0
        (if x.testBit c then upd B B Ts else Ts) := by
      cases hx : x.testBit c
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact h
      · simp only [Bool.true_and, ↓reduceIte]
        exact upd_rep B j Ts 0 m B h (by rw [Bool.and_self, decide_eq_true (Nat.zero_le m), Bool.true_and])
    have h2 := ih (c + 1) _ _ h1
    simp only [run]
    have e : (m + ∑ i ∈ Finset.range (B :: cs).length,
          if (x.testBit (c + i) && ((B :: cs).getD i 0).testBit j) then 1 else 0) =
        (m + (if (x.testBit c && B.testBit j) then 1 else 0)) + ∑ i ∈ Finset.range cs.length,
          if (x.testBit (c + 1 + i) && (cs.getD i 0).testBit j) then 1 else 0 := by
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
      have hs : (∑ i ∈ Finset.range cs.length,
            if (x.testBit (c + (i + 1)) && (cs.getD i 0).testBit j) then 1 else 0) =
          ∑ i ∈ Finset.range cs.length,
            if (x.testBit (c + 1 + i) && (cs.getD i 0).testBit j) then 1 else 0 :=
        Finset.sum_congr rfl (fun i _ => by rw [show c + (i + 1) = c + 1 + i by omega])
      rw [hs]
      ring
    rw [e]
    exact h2

theorem rep_getD (j m : ℕ) : ∀ (Ts : List ℕ) (k idx : ℕ), Rep j m k Ts → idx < Ts.length →
    (Ts.getD idx 0).testBit j = decide (k + idx + 1 ≤ m) := by
  intro Ts
  induction Ts with
  | nil => intro k idx _ h; simp at h
  | cons t ts ih =>
    intro k idx h hidx
    simp only [Rep] at h
    cases idx with
    | zero => simpa using h.1
    | succ idx =>
      simp only [List.getD_cons_succ]
      rw [ih (k + 1) idx h.2 (by simpa using hidx)]
      have e : k + 1 + idx + 1 = k + (idx + 1) + 1 := by omega
      rw [e]

theorem colOf_testBit (c : ℕ) : ∀ (ws : List ℕ) (j : ℕ), (colOf ws c).testBit j = (ws.getD j 0).testBit c := by
  intro ws
  induction ws with
  | nil => intro j; simp [colOf]
  | cons x xs ih =>
    intro j
    cases j with
    | zero => simp [colOf]
    | succ j => simp [colOf, Nat.testBit_bit_succ, ih]

theorem rowsOk_sound (cols : List ℕ) (s : ℕ) : ∀ (xs : List ℕ) (i0 : ℕ), rowsOk cols s i0 xs = true →
    ∀ idx < xs.length, (run (xs.getD idx 0) 0 cols (List.replicate (s + 1) 0)).getD s 0 = 2 ^ (i0 + idx) := by
  intro xs
  induction xs with
  | nil => intro i0 _ idx h; simp at h
  | cons x xs ih =>
    intro i0 h idx hidx
    simp only [rowsOk, Bool.and_eq_true, beq_iff_eq] at h
    cases idx with
    | zero => simpa using h.1
    | succ idx =>
      simp only [List.getD_cons_succ]
      rw [ih (i0 + 1) h.2 idx (by simpa using hidx)]
      congr 1
      omega

/-- `d(x,y) + 2|x ∩ y| = |x| + |y|` for binary words. -/
theorem ham_add {n : ℕ} (x y : Fin n → Bool) :
    hammingDist x y + 2 * (Finset.univ.filter (fun c => x c = true ∧ y c = true)).card =
      (Finset.univ.filter (fun c => x c = true)).card + (Finset.univ.filter (fun c => y c = true)).card := by
  simp only [hammingDist, Finset.card_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  cases x c <;> cases y c <;> simp

/-- word `j` of the list, as a function on coordinates. -/
def word (words : List ℕ) (n j : ℕ) : Fin n → Bool := fun c => (words.getD j 0).testBit c

theorem sound (n M w s : ℕ) (words cols : List ℕ) (hw1 : 1 ≤ w) (hs : s < w)
    (hlen : words.length = M)
    (hcols : cols = (List.range n).map (colOf words))
    (hW : weightOk cols n M w = true) (hR : rowsOk cols s 0 words = true) :
    ∃ C : Finset (Fin n → Bool), C.card = M ∧
      (∀ x ∈ C, (Finset.univ.filter (fun c => x c = true)).card = w) ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * (w - s) ≤ hammingDist x y) := by
  have hcl : cols.length = n := by rw [hcols]; simp
  have hcol : ∀ c < n, ∀ j, (cols.getD c 0).testBit j = (words.getD j 0).testBit c := by
    intro c hc j
    rw [hcols, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
    simp [colOf_testBit]
  -- the counter value for word `x` against word `j`
  have hcount : ∀ x j : ℕ, (∑ i ∈ Finset.range cols.length,
      if (x.testBit (0 + i) && (cols.getD i 0).testBit j) then 1 else 0) =
      (Finset.univ.filter (fun c : Fin n => x.testBit c = true ∧ word words n j c = true)).card := by
    intro x j
    rw [hcl, Finset.card_filter, Finset.sum_range]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hcol c c.isLt j]
    simp [word]
  -- weights
  have hwt : ∀ j < M, (Finset.univ.filter (fun c => word words n j c = true)).card = w := by
    intro j hj
    simp only [weightOk, Bool.and_eq_true, beq_iff_eq] at hW
    have hrep := run_rep (2 ^ n - 1) j cols 0 0 _ (rep_replicate j (w + 1) 0)
    rw [hcount] at hrep
    have hlenT := run_length (2 ^ n - 1) cols 0 (List.replicate (w + 1) 0)
    rw [List.length_replicate] at hlenT
    have e1 := rep_getD j _ _ 0 (w - 1) hrep (by omega)
    have e2 := rep_getD j _ _ 0 w hrep (by omega)
    rw [hW.1, Nat.testBit_two_pow_sub_one] at e1
    rw [hW.2, Nat.zero_testBit] at e2
    have hfil : (Finset.univ.filter (fun c : Fin n => (2 ^ n - 1).testBit c = true ∧ word words n j c = true)) =
        Finset.univ.filter (fun c => word words n j c = true) := by
      apply Finset.filter_congr
      intro c _
      simp [Nat.testBit_two_pow_sub_one, c.isLt]
    rw [hfil] at e1 e2
    simp only [hj, decide_true, zero_add] at e1
    have e1' := of_decide_eq_true e1.symm
    have e2' : ¬ (0 + w + 1 ≤ 0 + (Finset.univ.filter (fun c => word words n j c = true)).card) := by
      intro hh; rw [decide_eq_true hh] at e2; exact Bool.false_ne_true e2
    omega
  -- overlaps
  have hov : ∀ i < M, ∀ j < M, i ≠ j →
      (Finset.univ.filter (fun c => word words n i c = true ∧ word words n j c = true)).card ≤ s := by
    intro i hi j hj hij
    have hr := rowsOk_sound cols s words 0 hR i (by omega)
    have hrep := run_rep (words.getD i 0) j cols 0 0 _ (rep_replicate j (s + 1) 0)
    rw [hcount] at hrep
    have hlenT := run_length (words.getD i 0) cols 0 (List.replicate (s + 1) 0)
    rw [List.length_replicate] at hlenT
    have e := rep_getD j _ _ 0 s hrep (by omega)
    rw [hr, Nat.testBit_two_pow] at e
    have hne : decide (0 + i = j) = false := by simp; omega
    rw [hne] at e
    have e' : ¬ (0 + s + 1 ≤ 0 + (Finset.univ.filter
        (fun c : Fin n => (words.getD i 0).testBit c = true ∧ word words n j c = true)).card) := by
      intro hh; rw [decide_eq_true hh] at e; exact Bool.false_ne_true e
    change ¬ (0 + s + 1 ≤ 0 + (Finset.univ.filter
        (fun c : Fin n => word words n i c = true ∧ word words n j c = true)).card) at e'
    omega
  have hdist : ∀ i < M, ∀ j < M, i ≠ j → 2 * (w - s) ≤ hammingDist (word words n i) (word words n j) := by
    intro i hi j hj hij
    have h1 := ham_add (word words n i) (word words n j)
    rw [hwt i hi, hwt j hj] at h1
    have h2 := hov i hi j hj hij
    omega
  let f : Fin M → (Fin n → Bool) := fun j => word words n j
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hne' : (a : ℕ) ≠ b := fun e => hne (Fin.ext e)
    have := hdist a a.isLt b b.isLt hne'
    have h0 : hammingDist (word words n a) (word words n b) = 0 := by
      have : f a = f b := hab
      simp only [f] at this
      rw [this, hammingDist_self]
    omega
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact hwt a a.isLt
  · intro x hx y hy hxy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
    have hab : (a : ℕ) ≠ b := fun e => hxy (by simp only [f]; rw [e])
    exact hdist a a.isLt b b.isLt hab

end CwA30

namespace CwA30

/-- the 532 codewords: bit `c` of a word is its coordinate `c` (`c < 30`). -/
def words : List ℕ := [797931, 1595862, 3191724, 6109317, 6383448, 10533489, 11774979, 12218634,
  12391497, 12766896, 17435559, 19148613, 21066978, 21270717, 23549958, 24437268,
  24782994, 25533792, 34871118, 35103369, 37942353, 38297226, 42133956, 42541434,
  47099916, 48874536, 49565988, 51067584, 59265117, 61604619, 68636193, 69742236,
  70206738, 71896017, 72426543, 75884706, 76594452, 81925143, 84267912, 85082868,
  92299623, 94199832, 97749072, 99131976, 100763037, 102135168, 108363873, 118530234,
  122560833, 123209238, 128092449, 134616693, 137272386, 139484472, 140105217, 140413476,
  142935507, 143792034, 144853086, 151769412, 153188904, 163850286, 165020037, 168535824,
  170165736, 170430999, 175180299, 180367539, 184599246, 188399664, 195498144, 198263952,
  201526074, 204270336, 205685481, 216727746, 219433227, 221807877, 224401497, 237060468,
  243934341, 245121666, 246418476, 256184898, 275071381, 281707306, 294979156, 312527491,
  321522856, 337203301, 352736281, 356619526, 374610256, 405971146, 424699201, 437037106,
  444803596, 480785056, 1220041, 1663667, 2440082, 3327334, 3545147, 4880164,
  6654668, 7090294, 7734979, 9760328, 12703771, 13309336, 14180588, 15469958,
  19520656, 22642891, 25407542, 26618672, 28361176, 30939916, 33706937, 37767799,
  39041312, 43895041, 45285782, 46491139, 50435627, 50815084, 53237344, 56722352,
  61879832, 62464037, 67413874, 75535598, 78082624, 82724873, 87790082, 90571564,
  92982278, 93850801, 100871254, 101106439, 101630168, 102251267, 103493657, 106474688,
  106967749, 113444704, 119800999, 123759664, 124928074, 134827748, 135049561, 135990301,
  138085217, 140569613, 145539173, 151071196, 153101627, 156165248, 157463297, 159435541,
  165449746, 175580164, 181143128, 184770947, 185343361, 185964556, 187701602, 194118227,
  201742508, 202212878, 203260336, 204502534, 206987314, 210768541, 212949376, 213935498,
  226603201, 226889408, 231276841, 239601998, 247519328, 249856148, 268808775, 269010417,
  269182094, 269585378, 269928732, 270735300, 271422008, 273035144, 274408560, 275265833,
  275927565, 277634832, 280381664, 282096210, 283419674, 285248607, 286834208, 292327872,
  293355555, 294380033, 295756964, 297801417, 298403892, 302061758, 302843685, 305232960,
  305660633, 306643035, 307367175, 311453753, 316220288, 318275654, 320324610, 323078472,
  327167378, 328372328, 335688060, 337251914, 337417347, 342030464, 342885810, 344146377,
  344850614, 346298894, 354472050, 364005120, 368115852, 372213764, 373874699, 377721488,
  382278657, 385899300, 388309200, 398721585, 402839843, 402940664, 406068372, 406399238,
  411059759, 415113233, 415625472, 417336164, 419857298, 421265772, 421756973, 422119043,
  424162332, 437144129, 440508644, 455372805, 459574784, 467796248, 469855377, 473965335,
  475992072, 479313942, 479494977, 487007520, 496121858, 503363144, 505418123, 508182944,
  521144517, 529007714, 542425427, 547979942, 559088972, 581307032, 587549717, 616649477,
  623924417, 625743152, 638228522, 673865897, 696428042, 710977922, 714615392, 739586132,
  8901765, 10555305, 13215045, 16421025, 17803530, 18494535, 18630285, 21110610,
  21178005, 26430090, 27408525, 27477105, 29649105, 32842050, 34873845, 35607060,
  36989070, 37260570, 40456515, 42221220, 42356010, 44205645, 52860180, 54817050,
  54954210, 55216665, 59298210, 65684100, 69334305, 69747690, 70412625, 71214120,
  71766435, 72403365, 73960995, 73978140, 74521140, 75827325, 78160275, 80913030,
  84442440, 84712020, 85209705, 86065695, 88411290, 105720360, 109634100, 109908420,
  110433330, 118596420, 131368200, 138668610, 139495380, 140825250, 142428240, 143464995,
  143532870, 144806730, 147921990, 147956280, 149042280, 151654650, 154445985, 156320550,
  161826060, 168884880, 169424040, 170100945, 170419410, 171198225, 172131390, 173297865,
  176822580, 177250575, 205950225, 211440720, 219268200, 219816840, 220866660, 222843015,
  237192840, 245639235, 257037345, 262736400, 537580227, 537678127, 538289542, 538485342,
  539708172, 540099772, 541893537, 542545432, 543328632, 545416477, 546916162, 548219952,
  549464907, 549786352, 553962042, 556728517, 556961412, 558152707, 559568992, 562058902,
  562701792, 567312997, 571053172, 576586122, 577051912, 579434502, 579765267, 582267072,
  583205037, 586157137, 587246892, 588532672, 589883457, 597755082, 605235432, 606116167,
  608944177, 611590297, 615563307, 616301332, 617232912, 621998092, 622659622, 627663232,
  629539162, 631604737, 635443362, 637622872, 639108457, 640194432, 642896002, 647370757,
  658639252, 662725257, 671443297, 671492247, 673599952, 675361422, 677385637, 681017442,
  681729537, 686309682, 692535817, 694255702, 695731752, 697594912, 705711267, 707125272,
  708448332, 710434837, 718455552, 722207412, 726338562, 734015812, 738374832, 738399307,
  741346002, 743517952, 748921092, 755508817, 757870602, 771852837, 780407592, 788579602,
  805518373, 805730378, 806154388, 807002408, 808698448, 809011253, 812090528, 812254993,
  812716138, 814786193, 815005903, 816222473, 818874688, 819203618, 820125908, 822517873,
  822676073, 823159303, 824266018, 824705438, 827138578, 832443008, 833100868, 834945448,
  839729378, 840045778, 840225313, 841012238, 841032013, 843225668, 844104508, 847256033,
  848970788, 859579648, 860390533, 860895368, 864584528, 868372483, 872468233, 873341453,
  874152388, 874785188, 875144258, 876718108, 876757658, 881144968, 881346643, 882902648,
  886186273, 889205698, 889424003, 892635208, 913852928, 915474698, 916484368, 923862688,
  931438598, 939630098, 941376538, 942998408, 944264008, 944373863, 944982148, 948129848,
  948208948, 948450563, 956983568, 957386918, 960498928, 967066178, 971057153, 973105028,
  973541638, 977544233, 979964048, 981582913, 1009057843, 1011096193, 1022399488, 1025643028,
  1027662368, 1041399833, 1042419008, 1057570828]

/-- the 30 columns of the code (column `c` has bit `j` iff word `j` has coordinate `c`). -/
def cols : List ℕ := [1957353925511386079818766794160902736499256595139327555440459521448965743561714560150727260822712890453846097293187549720456170667367334069204578123036268965225,
  58915958481439904954539887862509786133859246486560108761707621281739601677504249102063244060226698918522129367050437100996626504279482717758225778523689538755,
  7474174203050001768704741142663589171399885995578717151660540991671793501488449714607588319651404292220306462412887292123887360345449313644618337943907262065678,
  8793813981341417146455787496504096422857857149808051677609058755780086141237000101664509765533840178537742008827185594536484513530600545250615027492790727352725,
  2265671823225326723216178799620471679428469058805812939250850073434492792234142955073210645919542573136751384720858012901261249977082996398109768759856600293938,
  940820881011707408317341095459827617353022448229906195645704260081430514764897077415762534167673004502041214082230003530273110425034281920217894019495352219173,
  3542881683575376008550808390460496418688346037656578459927722054910350184874648914434134591638271063717121552704962382379281321654522136555373629922638894078259,
  125608143089125502642830872596094808727569300803140934288134569848044172136082516342780127334922835343223165576038765428663574919398620927372634846193217254927,
  3520020132126233577374327762529221777115046081000563239426073843989604280011635242499907333585789366073429385621398688610285319026629815202193736209373052931222,
  1430024554291870502225592238121882380891667006028671343081809836327681692603712765683390405997062618368432454579816024508468651322164285276754601710386183704116,
  3770745203741314776969883259214383326086502235515110249294982685644890443608869645919159723792723215403078116880560668241855736626307951275118708223531308948305,
  3625742889450138950519785662527968351808050025442627581664245520327463564411379511366205681730639419826377040862806530678167027902689283496908616743614985490027,
  786161070333150901749639794237785673639171491156169488853880232744773957116668850060464361951948702307638364200628682159442799557231517775408794954851002249646,
  888213710245742892593016541808990812729743738005551449745554124258560986902744010861176156483799975423046499530919026525525082716557051036655450422725488253181,
  7937916095383626824466477563328506217754146424902381085112328525322075956818345910087079567289607220413043784768017530645625726575668393484192031486884604596882,
  2883335847114669641233189268881670916294148402857809333545953142559074049904250539822313955392927090107566267493066205216153146293466016465537418731397863613028,
  7129961082939016550466972929237893442501096058281798706929708845199237350273174930273456580749759973715481618730356376900507630351314402310172615395189650510168,
  5715009416159414490230278519892060338177996012341174846511089402742771652544197893858141932938729862755582956756778127490426953376971442661077281001620498892480,
  175495480524537995865681623586267493439517247234036611945988985407122248409691665651952186127339438809299331247737678932498857802054177807561187619818181683465,
  7043365572931575569025243696272940242062057830283222619315350098746395970468534723808626202800362293307957150969603990058072513893725080961694033756968227767691,
  1977173006873447606292148886353441044412304180785694885525361391637175235144297939134147777923429841919410597872051861061524358938696835011806497704097174356430,
  4243732540626732449380329931914981595887438096163240136087203825791045901457664722604559388746131139709921561699899684525427135620491642843217428498085000104436,
  1229877275211039975091146023418293740791868468653919645616908114361625966102763290829746219760307596406962158609596882916013899237282277342443275679356136059416,
  248466865052079610975431045248131162315863990961299640490712084868700394385204022292891275951253262008794991986483398533775534851449497802150099384209523213280,
  8349256604327919227455500814417487704714358003457759520419829355522588782638899255364491289498576342965467941000285593923028346796224173997635334833727070272512,
  12354919690295373459031964519077497015114929199517765626782319081544782716160324823540847152581338695813299465575358847017235135893179371334444374615378431311872,
  14004187331414743479332397973174225570322742544598135594724765433367783845233097762952023336462476602626277250916546040875160843949579936813681720047422454890496,
  14059105503198989243606393722935346629170209131870224142986366835860681229221364999312073740268285347159941911203579584624082542419516235341344902545580167790592,
  14059105607947488696282932109679969013360912945369681590435326810770631752280339431827902342447154928932262038452956261689491134889043948737049169068465405820928,
  14059105607947488696282932836518693308967803494693451901758536783080346207910793515675690483213011743645706399084433047006211839593638503349350333823115583291392]

theorem words_length : words.length = 532 := by decide +kernel

theorem cols_eq : cols = (List.range 30).map (colOf words) := by decide +kernel

theorem weight_ok : weightOk cols 30 532 11 = true := by decide +kernel

theorem rows_ok : rowsOk cols 6 0 words = true := by decide +kernel

theorem main : ∃ C : Finset (Fin 30 → Bool), C.card = 532 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 11) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  obtain ⟨C, h1, h2, h3⟩ := sound 30 532 11 6 words cols (by norm_num) (by norm_num) words_length cols_eq
    weight_ok rows_ok
  exact ⟨C, h1, h2, fun x hx y hy hxy => by simpa using h3 x hx y hy hxy⟩

end CwA30

theorem solution : ∃ C : Finset (Fin 30 → Bool), C.card = 532 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 11) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  exact CwA30.main
