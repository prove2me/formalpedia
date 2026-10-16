-- Prove2me | solution 1 for ConstantWeightCode.A_32_10_10_ge_527
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T01:39:02.498466+00:00
-- url     : https://prove2.me/submissions/8f5c8e03-00f1-40a4-bbd4-470676c02849

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

/-- the 527 codewords: bit `c` of a word is its coordinate `c` (`c < 32`). -/
def words : List ℕ := [4500321, 9000642, 18001284, 19989715, 29428505, 35009031, 36002568, 39979430,
  40468785, 58857010, 67249499, 70018062, 72005136, 79958860, 80937570, 93094337,
  117714020, 134498998, 136747027, 140036124, 144010272, 156680705, 159917720, 161875140,
  186188674, 209830155, 235428040, 268997996, 272114019, 273494054, 280072248, 288020544,
  313361410, 319835440, 323750280, 359407633, 372377348, 403902541, 411199873, 419660310,
  442518593, 470856080, 537995992, 544228038, 546988108, 560144496, 576041088, 626722820,
  637846547, 639670880, 647500560, 718815266, 727777417, 744754696, 763626021, 807805082,
  813712555, 822399746, 831535137, 839320620, 885037186, 907020437, 941712160, 1075991984,
  1083736681, 1088456076, 1091246339, 1093976216, 1107366573, 1120288992, 1142115337, 1152082176,
  1178656901, 1209798833, 1253445640, 1275693094, 1279341760, 1295001120, 1392665097, 1437630532,
  1455554834, 1480598101, 1489509392, 1527252042, 1615610164, 1619364993, 1627425110, 1644799492,
  1663070274, 1678641240, 1770074372, 1814040874, 1883424320, 724593, 1449186, 2898372,
  5796744, 11593488, 23186976, 46373952, 92747904, 121143307, 134263015, 185495808,
  242286614, 268526030, 370991616, 473957767, 484573228, 537052060, 741983232, 820449281,
  947915534, 969146456, 1074104120, 1134313477, 1140873331, 1310720707, 1483966464, 1640898562,
  1644178489, 1729102177, 1895831068, 1938292912, 6961193, 13922386, 27844772, 42995015,
  55689544, 85990030, 111379088, 171980060, 222758176, 235552821, 269305605, 343960120,
  445516352, 471105642, 538611210, 595759117, 604197313, 685810691, 687920240, 891032704,
  942211284, 1077222420, 1095239331, 1191518234, 1208394626, 1371621382, 1375840480, 1416647169,
  1621361489, 1782065408, 1884422568, 2155952213, 2164420778, 2167952641, 2181357908, 2188421634,
  2215232168, 2229359620, 2236616743, 2282980688, 2311235592, 2325749838, 2418477728, 2474987536,
  2504016028, 2620031105, 2686471701, 2689471808, 2802491424, 2819101573, 2852259041, 2860548408,
  3092578562, 3225459754, 3231459968, 3265792019, 3457499200, 3490719498, 3557034434, 3573613168,
  3780379657, 4037673476, 2152374535, 2156013101, 2157265422, 2164542554, 2166403633, 2167047196,
  2181601460, 2183539969, 2185323618, 2186610744, 2194195465, 2206223009, 2215719272, 2216428117,
  2219596290, 2223163588, 2225737840, 2240907282, 2264962370, 2282883875, 2283954896, 2285372586,
  2291708932, 2298843528, 2303992032, 2307604545, 2334330916, 2336243987, 2353041497, 2382441092,
  2418284102, 2420426144, 2421758081, 2423261524, 2435934216, 2441613835, 2450203408, 2460500416,
  2467725442, 2504134145, 2521178184, 2525004326, 2558599346, 2561934353, 2617398536, 2686486923,
  2689084556, 2693368640, 2696032514, 2699039400, 2701590677, 2724384784, 2735744022, 2752923168,
  2773517184, 2787967236, 2822881317, 2853203977, 2860784642, 2894872720, 2902525004, 2969715044,
  2976385058, 2989556289, 3020165425, 3087313424, 3223670915, 3225490198, 3230685464, 3239253632,
  3244581380, 3250595152, 3255697706, 3288925585, 3301285920, 3315605641, 3324004396, 3358362688,
  3368290565, 3399550720, 3428450824, 3490727109, 3498278986, 3558924306, 3574085636, 3642261792,
  3657566360, 3759319105, 3791946440, 3805286468, 3831628930, 3892847202, 4027143200, 1951811,
  3903622, 4294223, 7807244, 8588446, 15614488, 17176892, 31228976, 34353784,
  34656977, 51158529, 62457952, 68707568, 69313954, 70255545, 70562881, 100693793,
  102317058, 105840771, 110528545, 124915904, 136383789, 137415136, 138627908, 140511090,
  141125762, 201387586, 204634116, 211681542, 221057090, 249831808, 272767578, 274830272,
  277217399, 277255816, 281022180, 282251524, 331358403, 378020109, 402775172, 409268232,
  423363084, 442114180, 499663616, 503383577, 545535156, 549660544, 554434798, 554511632,
  562044360, 564503048, 570966859, 631375939, 662716806, 756040218, 805550344, 818536464,
  846726168, 876677225, 884228360, 956850183, 999327232, 1006767154, 1074717729, 1075888935,
  1091070312, 1099321088, 1108869596, 1109023264, 1124088720, 1126662209, 1129006096, 1141933718,
  1212350523, 1239421025, 1262751878, 1325433612, 1359225253, 1389429793, 1512080436, 1552166915,
  1611100688, 1611686291, 1637072928, 1679917085, 1693452336, 1753354450, 1768456720, 1849825281,
  1879584969, 1913700366, 1998654464, 2013534308, 4547737, 9095474, 15993033, 18190948,
  18423869, 31986066, 36381896, 36847738, 63972132, 72763792, 73695476, 76354601,
  86057797, 127944264, 145527584, 147390952, 152709202, 169116813, 172115594, 180957697,
  210771585, 219425033, 255888528, 269003923, 270434585, 277979781, 291055168, 294781904,
  295863585, 302239779, 305418404, 308544043, 320868697, 338233626, 344231188, 361915394,
  419465929, 421543170, 438850066, 511777056, 538007846, 540869170, 541476879, 555959562,
  558385361, 579150115, 582110336, 589563808, 591727170, 604479558, 606365857, 610836808,
  617088086, 641737394, 676467252, 688462376, 723830788, 747839505, 838931858, 843086340,
  843874373, 877700132, 1023554112, 1076015692, 1081738340, 1082953758, 1111919124, 1116770722,
  1158300230, 1164220672, 1179127616, 1183454340, 1208243785, 1208959116, 1212731714, 1221673616,
  1224861713, 1228013845, 1234176172, 1283474788, 1344480263, 1352934504, 1363316881, 1376924752,
  1447661576, 1495679010, 1677863716, 1686172680, 1687748746, 1745981955, 1755400264, 1946732801,
  2047108224, 2160362131, 2173240614, 2190672265, 2198997580, 2233860882, 2250511512, 2298816003,
  2320238116, 2353539376, 2421317681, 2450148358, 2466351365, 2492992584, 2550941737, 2559595104,
  2695151714, 2752813068, 2764071489, 2785219082, 2838501520, 2954399826, 2971706560, 3227664713,
  3242819780, 3296891649, 3358142488, 3380659330, 3422954516, 3529519392, 3761316004, 3795929472,
  21132357, 42264714, 82348549, 84529428, 144724125, 164697098, 168102353, 169058856,
  289448250, 329394196, 336204706, 338117712, 487669921, 542154001, 557458049, 573051943,
  578896500, 658788392, 672409412, 676235424, 975339842, 1084308002, 1114916098, 1146103886,
  1157793000, 1317576784, 1344818824, 1352470848, 1360267795, 1753875721, 1950679684]

/-- the 32 columns of the code (column `c` has bit `j` iff word `j` has coordinate `c`). -/
def cols : List ℕ := [164767731054967995786084576594884706180723343615656950108831068298205712347380967497775901551922286340473291841991531044558510806929021900653390006316993643833,
  58143227921921183985782528283448364696373114898387802601005836058048812780573682840272867126603387580834015063165858637245825993446060362593592129976164306602,
  221463578229085904328669109921873547386088519117827286194362450508455307537511232606776747595064919039208742604139345521776900185100222800208697207005962250404,
  128741860537657703212519191943623923450529470710401002906756651814146571190096631863610450869558599220207717529210528837928449838515524620731349505241726331984,
  61798856861625280348622387559216456074888217126169117605504539905869194163106252652485814384488623882446414436427328215408194651407465285512045324307079763736,
  4016764598112565088651323137962802331902625291086843402317530877648873786765559799359004751505506990164335909145846406506251787947363423389054907686541542273,
  39754582805942955598396414850313673564605927317437553860185041882971416090627423093607686980566340479131759854280236858623397416234401596522652157883325735947,
  236947198111931890690742259465451385066758103370837043339030116052585750813192279668857501795186506171141448950108868163459598410789012991785113999383577395342,
  138424161776089943816187236553039614398211013402767271752918658888193280213240763272576587651885402016045986478202345820574347734509718849932782231523264865749,
  288821179074984768061989325725535663325388023547647828990648316930376299343921126808902568295085046640885646682798700711202679482915639789816246540789562372723,
  127919293296354854298518945071171905678927163696507415269901099739460959215731367165704283230733533031840961827687216834620691766661302561425653758570729119246,
  70902283481462194986918197879091044843301935988309098426987944750260130094937938585389104937767247819440006118147164450508316434735350983336609325946247250133,
  27923657179100642511604182949339617667994524105653313404437478820239309154260577879445912533686863664763462660292599048897090728382700287698636265481170072162,
  9067214129174265617805835725964294523655613797471864793611783962210773785883142989414448208236240130938674394023425355034871797971633712169604612464164543525,
  14629181066511934192450010087506692384672255556995116725724249412849054015946181273607435593575089685668158472798707896936800576866825785520372773964935202882,
  10620741291197243404246193584805834089027711219546651291439993216599140985602308464805182360844349993410108599918855589668730551423852811239624671576908927237,
  247576478030008500733205784862985602922102854943698689473521270251454058643520826156628185818305996560644305536145683548509986102799900480829678622628096524634,
  113595060380473837298730031861452522497919207776106496951121433764738870179081650931206193954508345131602983144978124273358482265488330949155731049938979935908,
  303097338573813269063264931975855336459530738927123816983533752030937300160408680771882175051412925209406531999084107563883943131361894703409234161377308289121,
  158007876458529921553262020152345931379807013126904906558710834410799306739062305210326272198540334089891968566051403154001316565948768976296879390628518598914,
  85011400977016311157254763693354195451665705374639339964612915701700194367776846761274814369237555857606583090328358276550632266921496350576402792298954899500,
  15241853579166983426113624012463475992922415742305452169266443567235116024050820764793162009058634254640044247955951167763594389411334427892342930995700566472,
  222383638375062809930549146229355844111738357936922473393487521529405746778041066469481406963854327904667401301807385633493604976425822872485125717702386151825,
  144603324328632900852613007380802494653851999302718151570184705278763324232814344606657379252077142104008945060031380761189662457687590903749592395116788638226,
  58381951185203238809612174413985623714901423557903432112100461994496302012809566476052203669465063618695401299636376227220963845919464540983896836352684163612,
  7984494188533493697373059593966693608276252622283462858180459499629836435215392449205462051359977884909187940960380106163108268201715495147797780548536042464,
  231715205593732397477385135748963790666678350547008601709787515921858188525557090351283540698126560536634875043584656116869243186213390427877492357907209124864,
  117077865955542523370846562984312150725602572607152414161433953749202184710798337204238757394976043019861654331976340691463184825644461231412536891012240244736,
  315996840920504769957560116091546534730706545104515285815857940411338544306337141710098656572356375890457726636683173661462982134576888107535128936632473878528,
  329937661717872833507225864078898920198352779013763376293210191426532853258440162410726520245755363422787857849051716124103696889120675484048433913481561899008,
  438918000598788187925991907393622446581690835879923803772893384307837667772043991287591670463521507895483185943882621258621294599729220212251020852168235155456,
  204586912898240661604950569693643976866043597550891068914697557709764213334400271444064819117570255876051531186151718250531599113860658059405609140224]

theorem words_length : words.length = 527 := by decide +kernel

theorem cols_eq : cols = (List.range 32).map (colOf words) := by decide +kernel

theorem weight_ok : weightOk cols 32 527 10 = true := by decide +kernel

theorem rows_ok : rowsOk cols 5 0 words = true := by decide +kernel

theorem main : ∃ C : Finset (Fin 32 → Bool), C.card = 527 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 10) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  obtain ⟨C, h1, h2, h3⟩ := sound 32 527 10 5 words cols (by norm_num) (by norm_num) words_length cols_eq
    weight_ok rows_ok
  exact ⟨C, h1, h2, fun x hx y hy hxy => by simpa using h3 x hx y hy hxy⟩

end CwA30

theorem solution : ∃ C : Finset (Fin 32 → Bool), C.card = 527 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 10) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  exact CwA30.main
