-- Prove2me | solution 1 for ConstantWeightCode.A_29_10_12_ge_546
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T16:26:18.834628+00:00
-- url     : https://prove2.me/submissions/6679499b-d482-4737-aabd-d71946358ab4

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

/-- the 546 codewords: bit `c` of a word is its coordinate `c` (`c < 29`). -/
def words : List ℕ := [973085, 1946170, 3892340, 7019305, 7784680, 8703535, 10077665, 14038610,
  15569360, 17407070, 20155330, 24658535, 28077220, 28479595, 30412505, 31138720,
  34431845, 34814140, 37355995, 40310660, 43019035, 49317070, 54049825, 56154440,
  56959190, 59490835, 60825010, 62277440, 67352135, 68863690, 69628280, 74711990,
  75716825, 80621320, 86038070, 93164675, 98634140, 104223245, 105332795, 106040675,
  108099650, 112308880, 113829895, 113918380, 118981670, 121650020, 124554880, 126101105,
  134704270, 137727380, 138569495, 139256560, 146546995, 148457525, 149423980, 151433650,
  152895725, 155727245, 161242640, 163963145, 167893795, 172076140, 180800065, 186329350,
  186884125, 187238065, 191132675, 197268280, 203502475, 207491225, 208446490, 210665590,
  212081350, 216199300, 218164625, 224617760, 227659790, 227836760, 229784065, 235968965,
  237963340, 243300040, 249109760, 252202210, 8748337, 9086111, 11511329, 15883333,
  17323987, 17496674, 18103447, 18172222, 21219697, 22320097, 23022658, 31766666,
  34647974, 34993348, 36206894, 36344444, 38765653, 39601423, 41689769, 42439394,
  44640194, 46045316, 48375929, 51414397, 63533332, 65082697, 69295948, 69986696,
  71079697, 72413788, 72688888, 76800277, 77531306, 79202846, 79962463, 83379538,
  84878788, 86308933, 88686097, 89280388, 92090632, 96751858, 99927073, 102828794,
  118571977, 127066664, 130165394, 131272837, 138591896, 138760783, 139973392, 142159394,
  142879721, 143269451, 144827576, 145377776, 153600554, 154018439, 155062612, 158405692,
  159924926, 166759076, 169757576, 172617866, 174198959, 177372194, 178560776, 184181264,
  193503716, 199854146, 203598119, 205657588, 205852453, 211226947, 221317207, 236016787,
  237143954, 239831201, 244876331, 252226121, 254133328, 256655893, 260330788, 262545674,
  10371705, 20743410, 34850895, 41486820, 63459105, 69701790, 82973640, 126918210,
  139403580, 151643175, 165947280, 210039315, 239237385, 253836420, 5115571, 5501993,
  7706663, 10231142, 10753277, 11003986, 11072329, 15413326, 20462284, 21506554,
  22007972, 22144658, 30826652, 31887893, 34242181, 34938473, 37921741, 40924568,
  43013108, 44015944, 44289316, 50651371, 55118479, 58961089, 61653304, 63775786,
  66332933, 68484362, 69797183, 69876946, 75080837, 75669409, 75843482, 76589299,
  81849136, 83692097, 85879073, 86026216, 88031888, 88578632, 93857543, 101302742,
  106994717, 110236958, 117922178, 123306608, 127551572, 132665866, 136775513, 136968724,
  138071059, 139594366, 139753892, 150161674, 151338818, 151686964, 153178598, 159543413,
  161776967, 163698272, 167384194, 169116319, 171758146, 172052432, 172512377, 176063776,
  177157264, 181146499, 187715086, 202605484, 203253257, 213989434, 215106211, 218775887,
  220473916, 224790977, 235844356, 241770833, 243605671, 246613216, 255103144, 256020563,
  262228009, 265331732, 270061743, 271688030, 272019665, 274940604, 275603874, 279904653,
  281445752, 281694515, 282133355, 282772292, 285436685, 288558245, 291373850, 294456048,
  294953574, 295788035, 295831254, 297109128, 302437914, 308681034, 311007333, 311708867,
  314312244, 319595795, 320476640, 321471692, 321964625, 323140614, 323227052, 325782800,
  336440372, 338411619, 339794627, 340575017, 346187289, 348926612, 353579210, 354982278,
  360189032, 361138203, 367014305, 370756134, 370810989, 372517824, 374507928, 375493794,
  377845772, 378018648, 380686595, 383130144, 394315397, 403466327, 404445288, 408387782,
  409282713, 409502133, 411153798, 412714578, 416329473, 423939122, 424289889, 428233353,
  429417768, 437641265, 438332769, 438722964, 441529100, 449004557, 451942608, 453840950,
  458778753, 465593154, 470168619, 473076812, 473186522, 476600192, 480580400, 482552132,
  487256088, 487601840, 492937734, 497824832, 503519765, 520195338, 281454757, 290068693,
  294474058, 296364355, 310785349, 311701930, 320512660, 324293254, 338799145, 340952629,
  346131793, 353135242, 353673613, 354968404, 356853859, 372589864, 380151052, 409162834,
  413469802, 416617633, 423828130, 437835028, 438911770, 441501352, 445272262, 446862385,
  476744272, 491866648, 269078169, 269720882, 270023477, 271006308, 271611498, 273577160,
  274787540, 276195843, 276370067, 278718864, 281139624, 283956230, 284304678, 287912057,
  289002272, 293843792, 299477004, 300173900, 302070227, 304424463, 307388658, 308343333,
  309569088, 311625617, 319252128, 319263017, 320869277, 324016187, 329069057, 329662503,
  330518552, 331912344, 335704998, 335941325, 340413470, 345521289, 346341860, 348251210,
  348652775, 350702720, 352420787, 354815778, 370068800, 370090578, 373303098, 376046343,
  379596918, 389702658, 390889550, 392601648, 395389232, 402974540, 403447194, 406533377,
  406620489, 412391484, 419470569, 420647687, 422607122, 424248264, 428066964, 428870094,
  430443549, 432969984, 433266707, 436406118, 441196100, 442761843, 444645849, 456458627,
  471702144, 471745700, 478170740, 478759299, 483657230, 485068809, 489816377, 490758380,
  496664769, 507815105, 510969860, 513343644, 516767840, 522343008, 3560867, 4558283,
  5945731, 6337907, 7121734, 9116566, 11891462, 12675814, 14243468, 18233132,
  23294657, 23782924, 25277101, 25351628, 28486936, 28926091, 36466264, 44898331,
  46208567, 46589314, 47565848, 50554202, 50703256, 50727767, 56973872, 57852182,
  72932528, 73428139, 89796662, 90751193, 91424267, 92417134, 93178628, 94569317,
  95131696, 97261613, 101108404, 101233081, 101406512, 101455534, 104279057, 106275587,
  109841813, 112091329, 113947744, 115704364, 120328547, 120610997, 135998161, 136496869,
  137190593, 137386681, 145865056, 146856278, 148680773, 156666893, 157322011, 159581611,
  170931797, 179593324, 179929861, 181502386, 182848534, 184834268, 186357256, 187355521,
  189138634, 190263392, 194382001, 194523226, 202216808, 202466162, 202813024, 202911068,
  208558114, 212551174, 212878733, 214008533, 219683626, 224182658, 227895488, 231408728,
  240657094, 241221994]

/-- the 29 columns of the code (column `c` has bit `j` iff word `j` has coordinate `c`). -/
def cols : List ℕ := [2703322833038022780227217288197038491480727891696105866663493058834301964846397141320125565424607119721421753507828201408441813697054549579852411513452062680901737,
  184266631404668530464237241548408578831860176088464740253144497986611918751036015221531881552507682540559313047635795917645822172027004300544750078358051084616085154,
  60847998612828833965513682052693663967113680881450610852751354149557915170248436878755198523238324930130386402827416740567392620437121733001024136388119197676935717,
  148598934822979050150703354065943699580851090171110806725635166602068665356769654082806379801450465574835171972062216476719905996679421314910881175198479203446448699,
  30743945832189611432607431497792491497631031634155891021493081612295782567759306767374330969454869158968391272115774888836962587909821830471212034738008149768684423,
  119099991900020101907864796123512348065519210815864528951241469193103026086753551857434780966897496519522602334198316640207802656030178476144794024522100082030655614,
  217968100409109087238318343726437998095830687839584933896132659904722211370210457858012488455381196143468785759159018011247408133690449850569683153202528624782438356,
  81885202942512912910705345354883125757378713611131122120629562002424599960442687828729060233138358328523468656212964165148450288868385090074388212279189234875553104,
  127024502439756200699139168178332961038854284684630146252924396453429266557832779602804007346783242673384378489381390808167228233116087176494249190365713678236222793,
  63520155561753690700205069890949985876942430658144148119045431970701414744082937027082062954836351799895433556378597875200894713835154612908777146924837259431234730,
  30326649680394271599717724537297738425969384661532256119760951559979499927215502719014891623467475730963901133412681256086049832362051314677431833913186646456029924,
  18392991158426756830464791023825391254150615956802723655588122183973861128969337799637361778085435814900722810007803180886973755218505345773317110052856222775924281,
  3847695478413001939208895968618048501934938543754027664050071033399726641189973485626353387223845689344730168846989447907619134061516073178291535343935807120089995,
  72188245702943144247598676376122970008420896810268030740262167216045871860200114157957179416808804915877371424499445038106651859016632318728502677289856957846622342,
  138370273598004322333461293989334436746408859898590830377826559964674975480794139097870257637667096422821268577304173007479612233140839809838446794766882286873942133,
  124241018136722774768410067859776203812078681439839037819974455125408175340802184031732952680626301617383665166594770719235133282145658239419113902722504516136085363,
  45483226679274530178416136741676578651806405549898277747198488218112873688252698096106223301590069315444079537477257633175014268814827423242772022074011044148905806,
  29530988729986761377350345488207574187382795423484571953330635219248423416541075891435746908322722885822757929387107546019193805408160032806403418818990068523246749,
  21896350568663020008889901371328788584479169427987796438326689406356540092670575030796400676530668170146159732781764707285756571820265902988109287559978915327447475,
  97985609517262141970245180809251652482960285619029791477702071719357238721095523962629708981724510796648070782095500040732613204201906870003422900105561220206402383,
  83889197663018100846826750555031123739818656168255720636365211182740317375887546729833585966668631813390238356701735049004363833444371135166182270523326725547814102,
  116747332222328681293489703961880159655455976938023396439509371151622752206666157629008415760556996668478146210773396625093285331512208995251134699033014888085339420,
  210776831343814226540103703421100644941221360827875269753056677744009137559471928397476359586679633294860032274497290273018628375418173033086125048978594787177843096,
  46349461477370228933995049718263597751634860979256236062917214151719908180246271515682175915519565069568772164199790861565674449823814006532706916103160899528880608,
  54000917809227498212622737818379106788883011002286072228054578352212671762432634245412916477302696817058181747041034325192598736624311903807136548329538524853370368,
  172772345387018992956536982656857197078843216512069112828182596590309106899081792927404629630052905978797278793043096494746738415799222112756158465538116105304735744,
  230330327178355658494521320962484069017941986064487380775065511890616615936512898909698498317958906241622566474065425260497900045095064315781691548872123114347036672,
  230344386277259702817413934227154422397465478624902744163205447319116157315530468979027770850116595934976271879361378295854532631061951901701618486600629326318665728,
  11908525658859223294760121268437066290850060053501019099651816852276215084665797839087665278476660509683235538059488654697006810038471229440]

theorem words_length : words.length = 546 := by decide +kernel

theorem cols_eq : cols = (List.range 29).map (colOf words) := by decide +kernel

theorem weight_ok : weightOk cols 29 546 12 = true := by decide +kernel

theorem rows_ok : rowsOk cols 7 0 words = true := by decide +kernel

theorem main : ∃ C : Finset (Fin 29 → Bool), C.card = 546 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 12) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  obtain ⟨C, h1, h2, h3⟩ := sound 29 546 12 7 words cols (by norm_num) (by norm_num) words_length cols_eq
    weight_ok rows_ok
  exact ⟨C, h1, h2, fun x hx y hy hxy => by simpa using h3 x hx y hy hxy⟩

end CwA30

theorem solution : ∃ C : Finset (Fin 29 → Bool), C.card = 546 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 12) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  exact CwA30.main
