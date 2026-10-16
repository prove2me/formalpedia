-- Prove2me | solution 1 for ConstantWeightCode.A_32_10_10_ge_558
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T06:42:33.256963+00:00
-- url     : https://prove2.me/submissions/ac4baba5-1281-4780-850a-cca4063cf2f8

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

/-- the 558 codewords: bit `c` of a word is its coordinate `c` (`c < 32`). -/
def words : List ℕ := [755139, 1510278, 2173873, 2269471, 3020556, 4347746, 4538942, 6041112,
  8695492, 9077884, 10257289, 12082224, 17390984, 18155768, 20514578, 24164448,
  25445709, 34781968, 36311536, 41029156, 48328896, 50891418, 59310393, 69563936,
  71650563, 72623072, 75235605, 78562305, 82058312, 96657792, 96665623, 100675095,
  101782836, 118620786, 134353595, 139127872, 143301126, 145246144, 145334369, 150471210,
  151075079, 157124610, 164116624, 176454657, 177866257, 193315584, 193331246, 201350190,
  203565672, 237241572, 260055713, 268707190, 269717617, 275849255, 278255744, 286602252,
  290492288, 290668738, 300942420, 302150158, 314249220, 328233248, 352909314, 355732514,
  366510113, 386631168, 386662492, 402700380, 407131344, 436605205, 474483144, 478382337,
  520111426, 537414380, 539435234, 543232339, 551698510, 555679813, 556511488, 573204504,
  580984576, 581337476, 601884840, 604300316, 628498440, 646022213, 656466496, 675790865,
  698376465, 705818628, 711465028, 733020226, 773262336, 773324984, 784597257, 805400760,
  814262688, 822100567, 873210410, 945565697, 945816289, 948966288, 956764674, 990905381,
  1040222852, 1074119393, 1074828760, 1074876559, 1078870468, 1086464678, 1103397020, 1109567105,
  1111359626, 1113022976, 1122074635, 1124079371, 1140918621, 1146409008, 1149279363, 1161969152,
  1162674952, 1203769680, 1208600632, 1211666451, 1256996880, 1292044426, 1312932992, 1345357993,
  1351581730, 1396752930, 1411637256, 1422930056, 1466040452, 1484792107, 1546524672, 1546649968,
  1569194514, 1610801520, 1611180103, 1628525376, 1634779141, 1635781509, 1644201134, 1648381505,
  1679575049, 1746420820, 1816137877, 1879331875, 1891131394, 1891632578, 1897932576, 1913529348,
  1981810762, 2013407761, 2080445704, 38823305, 53233701, 77646610, 106467402, 151298251,
  155293220, 212934804, 273288369, 302596502, 310586440, 337207873, 371462787, 425869608,
  546576738, 550179337, 605193004, 621172880, 674415746, 742925574, 824218649, 851739216,
  1093153476, 1100358674, 1149390949, 1210386008, 1242345760, 1259473217, 1348831492, 1485851148,
  1648437298, 1703478432, 891925, 1783850, 3567700, 7135400, 14270800, 28541600,
  44041063, 57083200, 88082126, 114166400, 176164252, 228332800, 352328504, 456665600,
  471138331, 537093893, 671144385, 704657008, 864198659, 913331200, 942276662, 1074187786,
  1095762355, 1309310989, 1342288770, 1409314016, 1505841153, 1621623001, 1728397318, 1826662400,
  1884553324, 12622125, 17214753, 20077059, 25244250, 31724081, 34429506, 34915411,
  38150265, 40154118, 42158243, 50488500, 55091973, 56004737, 63448162, 67646825,
  68859012, 69830822, 76300530, 80308236, 84316486, 87102657, 100977000, 110183946,
  112009474, 126896324, 135293650, 136200483, 137718024, 139661644, 145098835, 152601060,
  160616472, 168632972, 170938473, 174097713, 174205314, 201954000, 202644037, 205582857,
  220367892, 224018948, 253792648, 270587300, 272400966, 273204239, 275436048, 276891309,
  279323288, 289802765, 290197670, 294133313, 305202120, 315627539, 321232944, 337265944,
  341876946, 348195426, 348410628, 377536665, 403908000, 404835397, 405288074, 411165714,
  411721861, 422379905, 440735784, 448037896, 507585296, 540026443, 541174600, 544801932,
  546408478, 550643905, 550872096, 553782618, 558646576, 579605530, 580395340, 587531921,
  588266626, 606093739, 609321603, 610404240, 631255078, 638079761, 639801377, 642465888,
  674531888, 683753892, 696390852, 696821256, 726155395, 755073330, 757137933, 807816000,
  809670794, 810576148, 822331428, 823443722, 844759810, 872809673, 881068085, 881471568,
  896075792, 1015170592, 1080052886, 1082349200, 1083780353, 1089603864, 1091199529, 1092816956,
  1094820945, 1101287810, 1101744192, 1107565236, 1117293152, 1141842065, 1146291241, 1159211060,
  1160790680, 1175063842, 1176533252, 1210343943, 1212187478, 1218643206, 1220808480, 1231555593,
  1262510156, 1276159522, 1279602754, 1284931776, 1343755045, 1349063776, 1367507784, 1376788693,
  1378402625, 1392781704, 1393642512, 1436819521, 1452310790, 1510146660, 1514275866, 1615632000,
  1619341588, 1621152296, 1644662856, 1646887444, 1678913795, 1689519620, 1745619346, 1762136170,
  1762943136, 1792151584, 1913198721, 2030341184, 2148807857, 2150132066, 2152209283, 2152466021,
  2152780484, 2156934918, 2157448394, 2158077320, 2160893971, 2166386188, 2167413140, 2168670992,
  2168807557, 2174304294, 2176331785, 2182351403, 2184775761, 2185288728, 2187342632, 2189858336,
  2190131466, 2197852215, 2201124940, 2205179922, 2217219158, 2217247289, 2222067874, 2223093808,
  2227201616, 2231536321, 2232233024, 2232436513, 2232779284, 2248220782, 2254766232, 2257985541,
  2262876196, 2281784139, 2284032133, 2286954668, 2287010930, 2296652100, 2298703968, 2306919584,
  2315588994, 2316982400, 2317389378, 2318074920, 2327906821, 2348957916, 2362048816, 2368487434,
  2378268744, 2386695233, 2416084630, 2419525121, 2420580618, 2424639559, 2426425688, 2426538212,
  2445820552, 2449924288, 2466355520, 2483183667, 2483694340, 2486481152, 2487295108, 2488666192,
  2508329994, 2518680845, 2550432184, 2550974977, 2571118083, 2576613984, 2589491220, 2609053840,
  2625906818, 2684685612, 2685600153, 2689685537, 2691566594, 2693677588, 2701795470, 2705367728,
  2705592776, 2711980033, 2718491681, 2729460353, 2744157456, 2752364928, 2777153859, 2785227392,
  2818883686, 2819905032, 2825478656, 2827106568, 2829848736, 2869176340, 2886770769, 2889878042,
  2953380720, 2954466306, 2957148485, 2969577577, 2994752518, 3005744320, 3031498792, 3070624032,
  3090155779, 3104329988, 3221887576, 3223588289, 3223716658, 3227930633, 3231887426, 3235649540,
  3238659349, 3239871528, 3246409755, 3256107292, 3263251808, 3263701904, 3276476418, 3288375717,
  3289499714, 3311437058, 3340831264, 3357246208, 3359803427, 3389075481, 3406824070, 3422971136,
  3433042689, 3490283724, 3492326416, 3503473664, 3506729488, 3512213824, 3536060577, 3590869032,
  3626057890, 3632272436, 3692561537, 3759277792, 3761448964, 3766813322, 3770688525, 3791671506,
  3827385361, 3842021388, 3864004992, 3915513936, 3993764416, 4032827910, 4061176328, 9495093,
  18990186, 37980372, 75960744, 118597641, 148112519, 151921488, 222316657, 237195282,
  283260161, 296225038, 303842976, 444633314, 474390564, 539244685, 566520322, 592450076,
  607685952, 671682083, 889266628, 948781128, 1078489370, 1133040644, 1147798083, 1184900152,
  1215371904, 1343364166, 1409582865, 1647640865, 1778533256, 1897562256]

/-- the 32 columns of the code (column `c` has bit `j` iff word `j` has coordinate `c`). -/
def cols : List ℕ := [180712672013676277446222575481650598983661933982231628833727666670884360218708971025435116204030828650469377491351469651262706844718278718161745801113180352099454616589,
  34222914866350649262638573523361128008686686255128285912200612806404878956954268316809584956347880678260788877721369080042163814398809969781522524334907367222117679211,
  31597237626857208769106640482962610136066867817626215969426013046811967548267351142996364538004138216524447752778194966000805880486933460949365473462955841663575589722,
  244662191082600971301660540125117839595834878001981495309283334071228787412413291440373337166695155661606497659655771719618981815841102154888817477629098502841123813080,
  539034856001765769764532866766717299214369465647916311545718809544196907382678070489047624481963654177873844040308016250948202099976687798119013963657742606546497858252,
  125428877878502936987031235016095702229838967656525873032932340340671851074651136335642602086613228325257463601400857905284188540013272685120808643481953996130776558180,
  33920097520256647365066249468299225671143336637176618091619935269182259955994958128221515649748022157616888458637017487906820238767537614520425313054913713543862133537,
  722600256719949583081201940922850760673354128987703262877885088670828811426929766291367154938889176495797714487666331411372950378921813399566266166345294747985645942023,
  413987154726617448001854595762781379929682754988591096644085316199520793345529276422724610584223770657563249332216667276486352044162602720962506072606317454485784843327,
  313427655832482833044149725633218655062442275221988480910179277457306573200336208371546228277763153287049223163050958992433831529284683075466041237772227592613849089526,
  97839917743417007570665786868897110752078540812201352154135114336334810295367093370071118504759696418316443864374398570268100854027676829288971581919623200620176563121,
  44420990177353726586323761015173976982653655873766120237673604836378449607298121135243161462852776816032929225969243561635288011599027036083616275284796063749111462278,
  47028386728882109273365199674829552096758659811922416986679261308265169467070030312232371071902567337724769882746230982587986575197134016040253369009291563553913215024,
  8548196963181776485773408608533998363772998869584483546515568153308590587267170516024819385044623871879846897891769814810971467506554752900916921968853660647665336716,
  239112939298654784018119839790044037173934935481124206821679253146798123297204493387601807061094668456894715531916234284764734824350689938002332746951238107401198573664,
  532619216205418968010729257605685920300791458575082415885887324378197228851689244971240729939938759559717165345086708149605124478491978238293395584634578188082025236233,
  133484697506960320424699281818257639936012053964820553995908542506753139451032315788723372493777810343570614329579815143177096075636119973162014597372768378294946000967,
  740791516246174554182956910813417418851045868407976112850550428239179974778358361043739106080970088859150589789853946423889920214457773819206207471913843810325496726075,
  177391316883524197834754886559889743921016582255121948291990078590949161662652109832334858114827890815430131211279402847870843956626320384964580248366845685781124687314,
  478829770828151764623634331724464790751734132430431388698118976977915194355325805570257969404431981928553802127116202715474638660999804113822585155974208732177717550737,
  633995051733643523168450226566703393400722034615759811657380642493713971385701858673347449778365247175170203249917081373074245068937833847124913250633085180194021108866,
  143800469727307788045770375935864248658552332162825644334797677650017309325364880938868335782884600382309729557188212804032857878700957283930510280831954635062022817820,
  19396014301529695022843478680245038858502271130111526657048539278658232805459430559036059689742114306221288350301615101837536784104390834263598481201162644337626480864,
  9691353165062075210272679978180287576825839936134775175617901078238111961509148563627788218160594484079523321284916789748290624740051465145634913847525345686327463680,
  473862134340232311726174268040638421747127375867883116566201119401659696910674166898584056091799065765981698816083408562300650853001357916507574142140731312550677966848,
  363054366724639416437470684019091783173799906315042605351519839225328645096733217196958980349720512886270231835504184693889592843368679709451635752841517300499720568832,
  70316402375794431838222011133924832772978968402769922749343002337784474115055165494997788017667328083383717174369034693179392659608050310026888078560490244920846581760,
  251196162904616110296170740593235103187325728853222269689332396434375840890157842163479423608983241881984732949308045375015167735580050151335996794042002814424714313728,
  560895554239288366793370642384174076689062521790703318365391764536550221058623165614029951145302107769210410869125932939023420522092731650019039869734964481069080903680,
  826468460152003136092759133992190480634499293731897391476973683296561078946651570751642042491096088101758446130804338916318003082491948555636976139435415228864352223232,
  942569229099609941689535581725333520816817430650606561121160722547851750122274188256110622494833124020005838924292333655906748469214758111104877191837526152735476416512,
  439347050248359021758841651141209165905243859199551915782204040486439451213000862871713021282004613328129900109658846747506371047554554106620725203012557996032]

theorem words_length : words.length = 558 := by decide +kernel

theorem cols_eq : cols = (List.range 32).map (colOf words) := by decide +kernel

theorem weight_ok : weightOk cols 32 558 10 = true := by decide +kernel

theorem rows_ok : rowsOk cols 5 0 words = true := by decide +kernel

theorem main : ∃ C : Finset (Fin 32 → Bool), C.card = 558 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 10) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  obtain ⟨C, h1, h2, h3⟩ := sound 32 558 10 5 words cols (by norm_num) (by norm_num) words_length cols_eq
    weight_ok rows_ok
  exact ⟨C, h1, h2, fun x hx y hy hxy => by simpa using h3 x hx y hy hxy⟩

end CwA30

theorem solution : ∃ C : Finset (Fin 32 → Bool), C.card = 558 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 10) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  exact CwA30.main
