-- Prove2me | solution 1 for ConstantWeightCode.A_30_10_11_ge_518
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T14:16:50.599796+00:00
-- url     : https://prove2.me/submissions/a414e1b1-fa3c-434e-a87b-cd7297818ef6

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

/-- the 518 codewords: bit `c` of a word is its coordinate `c` (`c < 30`). -/
def words : List ℕ := [3179951, 5317357, 6359902, 6462539, 8761091, 10634714, 11919457, 12719804,
  12925078, 17522182, 19066117, 19667111, 21269428, 21898627, 23838914, 24543881,
  25439608, 25850156, 35044364, 36622417, 38132234, 39334222, 42538856, 43797254,
  46238321, 47677828, 49087762, 50879216, 51700312, 59334853, 68438203, 70088728,
  71875393, 73244834, 76264468, 78668444, 81942577, 85077712, 87594508, 92476642,
  95355656, 98175524, 98590987, 101471113, 101758432, 103400624, 109218071, 112987169,
  118669706, 124266641, 125928493, 135807703, 136876406, 137448997, 138598273, 140177456,
  143750786, 144051283, 145167041, 146489668, 152528936, 157336888, 163885154, 168436829,
  170155424, 175189016, 183513221, 184953284, 188826763, 190711312, 196351048, 197181974,
  202121579, 202942226, 203516864, 206243369, 206801248, 218436142, 225974338, 228631109,
  235278517, 237339412, 248533282, 251856986, 4686903, 8839311, 9373806, 12985173,
  14422497, 17678622, 18524259, 18747612, 21645657, 25744707, 25970346, 27952689,
  28844994, 31526337, 35357244, 36260139, 37048518, 37495224, 38455461, 39208233,
  43144773, 43291314, 45230409, 51489414, 51940692, 55905378, 57689988, 63052674,
  70355157, 70714488, 72520278, 74097036, 74990448, 76722729, 76910922, 77895057,
  78416466, 84697653, 86289546, 86582628, 88283277, 89179683, 90460818, 93407817,
  102978828, 103881384, 105195813, 111810756, 115379976, 117733443, 126105348, 136561179,
  138637383, 140710314, 141428976, 143479857, 145040556, 147090081, 148194072, 149980896,
  152347797, 153445458, 153821844, 155790114, 156832932, 169395306, 172579092, 173165256,
  176566554, 178359366, 178807569, 180921636, 186815634, 193084449, 202498317, 203536419,
  205957656, 207762768, 210391626, 223621512, 230759952, 235466886, 235985937, 252210696,
  805458283, 805610198, 805914028, 806257073, 806521688, 807207778, 807737008, 808853533,
  809109188, 810167648, 812400698, 812912008, 815028928, 818094473, 818185753, 818438723,
  819495028, 820517648, 822143003, 824280643, 824751488, 829095973, 830882578, 831065138,
  831571078, 833683688, 835728928, 838979638, 840459313, 840470723, 843254918, 844196608,
  847992833, 852885578, 856458788, 856823908, 857835788, 862061008, 866151488, 872652908,
  873302023, 875612258, 875635078, 878362633, 881203468, 883086848, 890679298, 897585803,
  900464788, 905988653, 907611208, 908074243, 908341448, 910365208, 917504593, 918815648,
  926996608, 939600053, 939999448, 941297678, 945918148, 945963788, 946090273, 947942413,
  949011233, 951418898, 957100568, 957106273, 960867328, 973521923, 976052228, 985663813,
  989865238, 990908033, 995623208, 1006670938, 1009916048, 1010842118, 1011376528, 1015424048,
  1023631873, 1029702818, 1032324928, 1048686848, 465721, 931442, 1862884, 3725768,
  7451536, 8968733, 10035511, 10192073, 14903072, 15221869, 17937466, 18564001,
  20071022, 20384146, 28545031, 28588561, 29806144, 30443738, 33612647, 34828441,
  35874932, 37128002, 37907987, 40142044, 40768292, 52700897, 57090062, 57177122,
  57710881, 59612288, 59770651, 60887476, 67225294, 69351047, 69656882, 70914331,
  71749864, 74256004, 75815974, 80284088, 81536584, 105401794, 108134627, 109527587,
  114180124, 114354244, 115421762, 118067731, 119224576, 119541302, 121774952, 134450588,
  138702094, 139235483, 139313764, 141828662, 143499728, 148490243, 148512008, 151024051,
  151631948, 153171721, 160568176, 163073168, 164103053, 168893251, 169674893, 188285041,
  188981521, 193251593, 203835469, 208462849, 209729753, 210803588, 216269254, 218664353,
  219055174, 228360248, 228708488, 230843524, 236135462, 238449152, 239082604, 243549904,
  539250513, 541630114, 542136711, 542738181, 542976081, 546389316, 547402510, 547490725,
  548605450, 549081250, 551592115, 553796853, 554029701, 555907720, 557663241, 557934108,
  558110538, 560339988, 561291588, 566313318, 570722794, 571188490, 573024385, 574944528,
  578455570, 578997304, 579145821, 579350164, 583809064, 585712264, 588122635, 595755724,
  601112721, 604574676, 605446593, 605506068, 606634729, 608211261, 608269473, 609177858,
  613018144, 614548503, 620040228, 621123696, 621420730, 621814863, 621829416, 630747216,
  634553616, 639374358, 643940673, 654640536, 659166273, 665354530, 672278440, 673721539,
  674022274, 674141224, 676398546, 678449241, 679551610, 679668034, 681484804, 689165376,
  692226094, 696714501, 703209544, 705376480, 705970548, 706758814, 706787920, 709927435,
  713560615, 724623520, 732236320, 739513953, 741877804, 751010434, 757616901, 759433491,
  772410160, 781461634, 782369929, 793838148, 268524755, 268614054, 268792652, 269149848,
  269237525, 269864240, 270039594, 271293024, 271393419, 271643732, 274150592, 274351382,
  274852008, 279865728, 280267308, 281268560, 284447747, 289767785, 290458685, 291296000,
  291527237, 292099160, 294101664, 300460038, 304656429, 311100114, 312481914, 314156544,
  314619018, 315762864, 318772685, 319767872, 323747927, 332484620, 335744837, 340877402,
  341050127, 341317265, 344599563, 348128627, 352371665, 353764772, 356528372, 359877632,
  360802580, 363090272, 365768705, 369109914, 369468497, 371100288, 378619265, 379060398,
  389332997, 396533784, 402697833, 403054218, 404132165, 410659329, 413319348, 413664798,
  414199074, 420763670, 427821798, 430309419, 436307874, 438960519, 439094088, 440735237,
  442499769, 444621288, 451319808, 453169704, 457745088, 463101954, 469784372, 470501538,
  473765120, 483590165, 487915715, 488803074, 489685340, 510230538, 512393313, 524632112,
  275071381, 281707306, 294979156, 312527491, 321522856, 337203301, 352736281, 356619526,
  374610256, 405971146, 424699201, 437037106, 444803596, 480785056]

/-- the 30 columns of the code (column `c` has bit `j` iff word `j` has coordinate `c`). -/
def cols : List ℕ := [59144850349217144293055335340728543531961886466283226430582661002461494490474658246618278058977512645591819978669364602458532049893174151158785663818050651,
  141314855650988055927741358943592332198256335057883186991323966228384844399896099737699214105723389522415056094836850159000146071497432111419227233439476541,
  223170412315854536979185037096410792669617504864022556695757019603794822977229276665036532942845814338444643819630585595622937304663812810801259334766829447,
  245645060405698061851463073201626897211552590263063935309159754867964432976850121857960748970753550679989742439451652728001595772107828076898576961847656623,
  124314016244404048952581305285072389852744963352220626717365116029692953393088028412395148547090994744065742077400505053185703496147994740120843877970678180,
  538970472693710348207127545165464667669635957742995112091909323012012187875977430055870653060150781184188092169075519713849441528853629373035646687476127939,
  95757328397978793990292720783238368426503279376657760100080404356972305775278128166289151927510988977004064835343688633625526635298393669193926808472993902,
  457175761849720166385680120050918391828287055612623185587240982220350193563951203049502211135122697754286252007060752499997858094052240711637899629878639011,
  73905234134707921407166236130722695305481149128161246445154918277730315534726316708811563047480716816506578461947439868532610915447098369473446389854975029,
  644309728618546341449608657425171415244554333422640940213302453991414117251432966156972014993649764687510396369905961345424652751551155192428993705797522070,
  64734828849759932702588912675853147623348811554326050753216037772527476103764494480166805870886517964444173048507014757861173693673882730063479256476100281,
  336453922649610681528622819648391853291116125393746100964841149028512081657201553817295854453814700771578116560343112245530863181779514662613354294761824028,
  454189759356578538784966217136127064366263869527915817484809744011389296819061898787172119097751280519667925374290284083883959042176925780118439313551526792,
  831284131618408991456487402718684980360887631171698707360691602784798876349712984801431617149690940057444822615905924606823292741093463014452045139868591442,
  59156902078163580973735425132121437393412524811970234147166670480839188229032269508556799956814559517357291329618745747101172953700228829170957654553151072,
  141327025228316758786098691587645575508508523315303567024977916417534673839004527316828311557934697256267766584845643495919841059650494981270582924718953561,
  223200946841389644995597484677552791349023292679518089578924077284502694893719211689953881028317959939567387097792600886470189943212665513795025744199435094,
  245650508231279378262627884049956931530058084287162073394491728089032977680581559293782600783908235905587827083949222789117445520026509866385597212872599208,
  124311308487600010543561907628974716795115448885179215437028039788454456345532536485081562383366707920955792867550295329421881508160085467275479942443153744,
  538951015569730617677917397058804274138895827134237980231832289698962388713057403165368790873281001418732176971225448699583978946968851287327700796465375744,
  95744859582082800627729451932314737640040883520081196441363415649595606795812884812206619832599324342423589202906956395693367447305464327982077473785675843,
  457186491641637362384812430925546897246112140003240613349276598186437248685387876718791689482675336797640099745948079792065442470406017020738526016948456557,
  73933226626262715240765893534998306667516322662231588111659294362866081134942597878573829715934657002057225473327524896813291934177950771520775085016281486,
  644321553280998778290399378063008294998293350185589752313259558150451442201893395301826123825681520004052520549550622265789836428444825620993086075674231280,
  64766533017309747169271068661996821658671629677689085287976826816685196159040437157724985676800570387199922208583750477439126613126345970884505911412653568,
  336498058807336259820526572529130988313793558246416407097985151939863758289692445212045725885864357226426035505656133358869404878336308784742486431586058240,
  454241816729852343915354597919682159488057288045597951140072850333859466945698793166312191043865210466879122853238576996736907104447025746670042987697799168,
  831336465906118581122411073548004049279083758790675555181613819980951163324869094564441138136402820504129424046887966095365333943770390074557672986335248384,
  858099707516326214372737599882466466910514554256606131072605702219055752343285317878135610949500067224444296550010216366906156152446923969763226436614750208,
  2707685248164858261307044961718183793024382421581560575667731415103336516924524239825740313951063317193751615795620921978388480]

theorem words_length : words.length = 518 := by decide +kernel

theorem cols_eq : cols = (List.range 30).map (colOf words) := by decide +kernel

theorem weight_ok : weightOk cols 30 518 11 = true := by decide +kernel

theorem rows_ok : rowsOk cols 6 0 words = true := by decide +kernel

theorem main : ∃ C : Finset (Fin 30 → Bool), C.card = 518 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 11) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  obtain ⟨C, h1, h2, h3⟩ := sound 30 518 11 6 words cols (by norm_num) (by norm_num) words_length cols_eq
    weight_ok rows_ok
  exact ⟨C, h1, h2, fun x hx y hy hxy => by simpa using h3 x hx y hy hxy⟩

end CwA30

theorem solution : ∃ C : Finset (Fin 30 → Bool), C.card = 518 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 11) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  exact CwA30.main
