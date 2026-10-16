-- Prove2me | solution 1 for ConstantWeightCode.A_30_10_10_ge_333
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T03:53:03.998235+00:00
-- url     : https://prove2.me/submissions/7cbd25f3-9bb8-4ec4-8bc8-ee5b858a32c5

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

/-- the 333 codewords: bit `c` of a word is its coordinate `c` (`c < 30`). -/
def words : List ℕ := [1424768, 2849536, 4438120, 5666305, 8876240, 11299843, 12887142, 17719713,
  22566919, 25774284, 35406659, 35834530, 45101071, 51515801, 58779760, 70780551,
  71636293, 72406098, 75621960, 84460842, 90202142, 103031602, 117526753, 135849100,
  141561102, 143272586, 144779429, 151211153, 168888917, 180371517, 206063204, 235020739,
  271665433, 277402280, 283122204, 286545172, 289558858, 302389539, 337777834, 360710267,
  369132012, 402818992, 412093641, 470041478, 537566912, 539073588, 543298099, 554771793,
  566244408, 573057577, 574665508, 579084949, 604779078, 675555668, 721420534, 738264024,
  805637984, 806391322, 824187282, 940050189, 35094693, 37405713, 49321120, 59870211,
  70189386, 74778659, 78219794, 98642240, 102534240, 119740422, 122716721, 140378772,
  147030412, 149557318, 156439588, 177774881, 197284480, 205068480, 206213281, 239480844,
  245433442, 277786884, 280757544, 294060824, 299114636, 312879176, 319988776, 337873985,
  348424458, 355549762, 394536193, 410136960, 412426562, 478961688, 490866884, 504402949,
  554418258, 555573768, 561515088, 566806017, 575964425, 588121648, 598229272, 610369734,
  625758352, 639977552, 675747970, 696848916, 705807904, 711066757, 789072386, 814063657,
  820273920, 824853124, 842039395, 889758480, 943902740, 957890609, 981733768, 1008805898,
  26529865, 36024897, 53026963, 72049794, 78694444, 106053926, 137533961, 144066821,
  157356121, 172074192, 185107145, 212075085, 275067922, 288100875, 302818946, 314712242,
  344148384, 370214290, 407148104, 424150170, 550135844, 554883360, 576201750, 605637892,
  622891624, 629424484, 688264001, 740428580, 814296208, 848300340, 7121072, 14242144,
  27427126, 28451521, 54854252, 56903042, 84339716, 109708504, 113773317, 135103766,
  168646665, 219417008, 227546634, 270207532, 275300429, 289512193, 337260563, 419553442,
  438834016, 455093268, 540415064, 550568091, 579024386, 604406411, 674521126, 681627008,
  746631249, 839074117, 877668032, 910186536, 7766880, 15533760, 23299594, 31067520,
  46599188, 46960659, 62135040, 85623109, 93198376, 93921318, 111333696, 117806104,
  124270080, 140096002, 171246218, 186396752, 187842636, 210080544, 222634625, 235612208,
  248540160, 270368984, 280192004, 289841233, 296260688, 340895764, 342492436, 372793504,
  375652505, 417366659, 420161088, 428900964, 436437019, 445269250, 471224416, 497047553,
  540737968, 548504325, 560351241, 579682466, 592521376, 595757580, 606902529, 641894800,
  672039020, 681791528, 684984872, 707302410, 745554241, 751305010, 755089421, 811123074,
  834733318, 840322176, 857801928, 872874038, 890505733, 914415622, 942416065, 994062339,
  625123, 647733, 1250246, 1262699, 2492631, 2500492, 4985262, 5000984,
  8563993, 8574087, 9969201, 9970524, 17115407, 17127986, 19938402, 19941048,
  21007533, 21021652, 34223205, 34230814, 39849329, 39876804, 42010537, 42015066,
  68428861, 68446410, 79698658, 79720841, 84021074, 84030132, 136857722, 136860053,
  159397316, 159408915, 168042148, 168060264, 201365662, 201371171, 270576454, 270595361,
  273682677, 273687339, 318785063, 318794632, 336084296, 336087761, 402731324, 402742342,
  537183473, 537194778, 541152908, 541157955, 547365354, 547374678, 637537359, 637556497,
  672142755, 672168592, 805451917, 805462648, 14043, 23405, 28086, 53268516,
  94679170, 106504265, 140888580, 146056720, 152470722, 186747176, 189358340, 213008530,
  281744393, 292113440, 304941444, 306561328, 373494352, 378683913, 420268352, 425984293,
  440961062, 563488786, 584194113, 607298818, 609882888, 613089889, 630228116, 690135192,
  746988704, 757335059, 840503937, 851968586, 881922124]

/-- the 30 columns of the code (column `c` has bit `j` iff word `j` has coordinate `c`). -/
def cols : List ℕ := [3359115028097352166714255501328536487971627885320706599506051634016376952082700075478855492923667880,
  5491627405649554168172028138335827774461497858193779142631713303034488047708147889298704064191307104,
  8888945670155324166011677543716175513854342291572560601135053533949270390190559054327739117156275008,
  13431362939778932638033261525303190860466152041403549468232042835694104403566543446879493222676836868,
  1508211540274644244387384643717837289028205411782485557131943103987841806743635879121312860049924112,
  618452756528044150776124350846806032323136102159033971173659071447892627232874634987741085319055556,
  13201067971796457215638746587275722482522500152273178233578363645558701275082495403221473041475651156,
  3144211028683387724750107198042937274110423496152161630039119574277038108894754096654958840793574033,
  52968944840927151219721585280514120241440867387708912745564694925568853126849991314045152235431043,
  6664680448223267233160490846008334954752266522230389105505804068385356945287573443386478309060938762,
  1794254933920127059479801919116420750780503642407852418709245494279277945273466346948138900401389673,
  15537154561573319163097506808979335365288312640228440033639402023451405739619300847261275496925991,
  10979115263480805014412942641379349415451603633048809678885641914219461440021729311838137469443977503,
  841581348576703563747185410841640848469667528890872288900488738064203060496075040311738927263535359,
  890850155900699305119746541125335589630303218162671020592979428450274618700556542452151741206458,
  429936145018850186618046411226065226600565850710840623884995698599008202453265049775040689326671941,
  11004867188193714041372213240880616160097493109869175339645934841813307614019133178833907370942595607,
  953063754147986591774689590912741728352404545297827724606853683029706971134304454505820568653146270,
  1646413093810823129404292108602126648525152785042502465603241942459559486283087368334731504099853561,
  6667010109170026130753357661877158976056773006380978541194914749134837603687064934623296636708226978,
  11137308423309711045200072555179796624162377290575794318331722141538560108512343355871023863544591625,
  1385243309826607867342999838919256610086391777826699035521045950124445067877392155525242851788101666,
  4420652732207285400831379793233677607503024543827242751154209465204808228586903239673254418771542348,
  13888467514843338199232513971000024070439423344289940648930737972049207843879081998023872032186585712,
  1509629224293177692485099879888498659446191621371215521325969875463283901746701564887437731358598016,
  6572935941954392454489284756923963555340905924031083072398886689643392806727537181073939497075375104,
  10646164154322037093995492047003528968429737603767628123779471766493360250352272997697552808421588992,
  1917590575209371328878139519940319681109138643182821816817649000538864548300354229182240449326219264,
  15315018705381840044537347574356767152492214335732302320815674329042296561273148819531845777406033920,
  17493733826228792227913304074921769084223474040869463890821416414370117205051758859183318052005478400]

theorem words_length : words.length = 333 := by decide +kernel

theorem cols_eq : cols = (List.range 30).map (colOf words) := by decide +kernel

theorem weight_ok : weightOk cols 30 333 10 = true := by decide +kernel

theorem rows_ok : rowsOk cols 5 0 words = true := by decide +kernel

theorem main : ∃ C : Finset (Fin 30 → Bool), C.card = 333 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 10) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  obtain ⟨C, h1, h2, h3⟩ := sound 30 333 10 5 words cols (by norm_num) (by norm_num) words_length cols_eq
    weight_ok rows_ok
  exact ⟨C, h1, h2, fun x hx y hy hxy => by simpa using h3 x hx y hy hxy⟩

end CwA30

theorem solution : ∃ C : Finset (Fin 30 → Bool), C.card = 333 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 10) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  exact CwA30.main
