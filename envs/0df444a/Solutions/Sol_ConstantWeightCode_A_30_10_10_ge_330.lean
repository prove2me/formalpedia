-- Prove2me | solution 1 for ConstantWeightCode.A_30_10_10_ge_330
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T10:02:11.766309+00:00
-- url     : https://prove2.me/submissions/2d987c0d-4265-4cb4-b8a1-c218e40a2537

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

/-- the 330 codewords: bit `c` of a word is its coordinate `c` (`c < 30`). -/
def words : List ℕ := [3392523, 6752279, 13504558, 22187176, 26778641, 27009116, 42304417, 44374352,
  46321795, 53557282, 54018232, 68782529, 84608834, 88748704, 92610823, 107114564,
  108003697, 137565058, 168468581, 169217668, 177497408, 185221646, 205621404, 214196361,
  216007394, 234991136, 273974058, 275130116, 280032288, 310552601, 336937162, 338435336,
  346073606, 354962049, 370410525, 407933044, 411242808, 428359955, 432014788, 469982272,
  538567173, 547948116, 550260232, 558023120, 560031809, 571262176, 621105202, 639665230,
  654350096, 673841557, 676870672, 692147212, 709891331, 740821050, 806154498, 815866088,
  822485616, 856687143, 864029576, 939931777, 23519266, 47005765, 93978763, 187957526,
  218482048, 274323464, 375915052, 429951152, 436931329, 548614161, 646095552, 674016260,
  751830104, 859902304, 873862658, 128745604, 150323216, 257491208, 300613665, 373801472,
  421431298, 514982416, 601227330, 612016136, 723755264, 747570177, 842862596, 898732160,
  986220608, 1029964832, 7962790, 15925580, 23759428, 31851160, 47518856, 54952205,
  63702320, 73827521, 95037712, 107531280, 109481218, 109904410, 127404640, 147655042,
  190075424, 201830410, 215029793, 218962436, 219251219, 219808820, 254809280, 274367121,
  282173507, 286892336, 295310084, 295813952, 337027236, 352684073, 380118081, 403660820,
  430059586, 437924872, 438502438, 439617640, 446730501, 509618560, 540835923, 548734242,
  564347014, 573784672, 590620168, 591595137, 637769733, 646496521, 674054472, 677957665,
  680300696, 684761504, 705368146, 713212948, 760236162, 807288873, 855755778, 860119172,
  875849744, 877004876, 879235280, 893461002, 964732417, 1019237120, 5088281, 10176562,
  20320357, 21336770, 40640714, 42673540, 81281428, 85347080, 92455461, 162530089,
  170661393, 184878155, 226531656, 291549321, 325060178, 341322786, 369756310, 403281027,
  405316184, 453063312, 539415052, 547522913, 583098642, 650120356, 682645572, 738511425,
  739512620, 806562054, 810632368, 906126624, 837775, 1642783, 3285566, 6571132,
  10543317, 13109497, 16952195, 21053867, 26218994, 33904390, 42074967, 52437988,
  67776013, 84149934, 104875976, 134347025, 135552026, 168299868, 209719185, 268661283,
  271071285, 272689888, 336599736, 419438370, 537289799, 542142570, 545347009, 604044424,
  673199472, 838876740, 371532, 743064, 1453361, 2267354, 2906722, 4296050,
  4496933, 4534708, 5780677, 8592100, 8993866, 9069416, 11561354, 17184200,
  17987732, 18106065, 23089941, 25227802, 34368400, 35942697, 36179363, 46147115,
  50422837, 68704033, 71852627, 72358726, 75539772, 83932259, 92294230, 100812907,
  134796228, 137375299, 143672487, 144717452, 151079544, 167864518, 184555693, 201593047,
  269010486, 269559689, 274750598, 287312207, 289434904, 302126321, 335696269, 369111386,
  402703721, 403186094, 537040294, 537988205, 539002553, 539119378, 549468429, 574624414,
  578837041, 604252642, 671359771, 738222772, 805374675, 806372188, 10266242, 20532484,
  41032201, 44156972, 51042592, 82064402, 88281177, 102052417, 135505104, 164128804,
  176562354, 204104834, 239124774, 271010208, 281187912, 328224841, 338724242, 353124708,
  408176901, 478216781, 541987649, 558933014, 562375824, 604607080, 656416915, 677448484,
  706216649, 816321035, 839158068, 956433562, 48869888, 77516864, 97739776, 155000961,
  166233098, 195446785, 204374816, 256155728, 287806480, 310001922, 319520968, 332466196,
  390860803, 408749632, 489734156, 512311456, 561289472, 575612960, 619971077, 639041936,
  664932392, 680757768, 696615012, 781721606, 817499264, 877233412, 885162034, 975471234,
  979435545, 1024590145]

/-- the 30 columns of the code (column `c` has bit `j` iff word `j` has coordinate `c`). -/
def cols : List ℕ := [1640980465944354023458610164574110404155509753970464814506924667364421021102267814777706256422750547,
  427206827747629338141540792002431938092869969764011738797491927657370911040375879658663416254583559,
  94554973565260416147298896678915332386195459727346724096680506401490498248298236055356020095762470,
  553256137035831980575650495948179061065194009154095240371059507569802272053173799309934145874953261,
  684588800655814497031787413505599870999739568660481243447539601702213667777120123126329320333706418,
  147716984412313568711154881603097068123695470994438328178715122144567740272862028167973562715809356,
  1102188348819980217253199992637381181621253010924797039275472093864249361835405382964531507576019104,
  308718979692336396656132955085718290832874857944297664775979231966904957772729216045473667463392584,
  1163179614157202289675289148792802258180651791859882145402836347604551896466718382211262584611625152,
  278229131699286371740471787739974011641893211107137215622277376303356127065388396478006163585773632,
  102544628375464881147506924287816289356319898106647237459859245910952212852632112853638733677203481,
  38852501832029761392639067844246733014545022832304105639054146508387682913736417256529445532469914,
  2278357789969748262853807294444216889575319544159050942479954255620604120629963993799211369014164,
  17355181932702093256264024511995193426356467157192105236148368718907305656967078463407173917794848,
  101244762932146130353681511420714731164836735013724233591670630399701738822794364812654428587265,
  491446929998946995594851574559757188543838985052701402515039790228752894576659012617818885801118041,
  629405423277525673890048849798432381030869724553811083093588292633441722684578526711738593953602243,
  1272251137437091623547147040514713687491798020897863463649011187413730413136420136613763546891596047,
  283978806353410819445069377758671417478297339132952947316061143850824364276855883452251201963835622,
  119977367741645737598136030566845875407405142519531027254038698943432690822668604408008992660667444,
  1150951820450870741660250713657505961865203233372808101569313396787492033791273970229649540353035833,
  857233483425688856223727372009602127686456027275218503906977125642738639068804258451180951569663619,
  752832480471075426234001908333754760638557942253639435881116921405343630520056628311115031375880462,
  203523798916675000439486861359268703779612486238229114351195863895585414656597888849098637904462324,
  1104487678538738078700301888518291380084268227126640979547496823536712650543776590348728786523027000,
  840860619676805802809984046284838104183655513440155113320326790133242078856622445433664788005488576,
  1319614862914056127207046142423932635190716177702654299897752722792565346730896294508860219454519296,
  1943865520874974367399956472937783517103268738132554243209400605417797212531814993512971899431157760,
  2153207911701192710616386058766634138109224178613095463070511397430273286719167895103411786971348992,
  2187117227628313552777873899668049210420683924138000807689765535384401652160438477955445043511689216]

theorem words_length : words.length = 330 := by decide +kernel

theorem cols_eq : cols = (List.range 30).map (colOf words) := by decide +kernel

theorem weight_ok : weightOk cols 30 330 10 = true := by decide +kernel

theorem rows_ok : rowsOk cols 5 0 words = true := by decide +kernel

theorem main : ∃ C : Finset (Fin 30 → Bool), C.card = 330 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 10) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  obtain ⟨C, h1, h2, h3⟩ := sound 30 330 10 5 words cols (by norm_num) (by norm_num) words_length cols_eq
    weight_ok rows_ok
  exact ⟨C, h1, h2, fun x hx y hy hxy => by simpa using h3 x hx y hy hxy⟩

end CwA30

theorem solution : ∃ C : Finset (Fin 30 → Bool), C.card = 330 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 10) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by
  exact CwA30.main
