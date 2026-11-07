-- Prove2me | solution 1 for GTWSched.NPC.td_mem_NP
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T21:31:41.86319+00:00
-- url     : https://prove2.me/submissions/b1726159-4661-4332-b54a-df617b0ec9d5

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems
import Theorems.Thm_GTWSched_NPC_tdCheck_len_filter
import Theorems.Thm_GTWSched_NPC_tdCheck_cost_filter
import Theorems.Thm_GTWSched_NPC_tdCheck_overlap_filter
import Theorems.Thm_CookPvsNP_mem_P_of_polyReducible
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

set_option autoImplicit false


namespace TDNPRound

open MeasureTheory Set

lemma floor_add_eq (x θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ⌊x + θ⌋ = ⌊x⌋ + if 1 - Int.fract x ≤ θ then 1 else 0 := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hx : x = ⌊x⌋ + Int.fract x := (Int.floor_add_fract x).symm
  split_ifs with h
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith

/-- The step function that agrees with `θ ↦ |⌊x + θ⌋ - c|` on `[0,1)`. -/
noncomputable def gstep (x c : ℝ) (θ : ℝ) : ℝ :=
  |(⌊x⌋ : ℝ) - c| + (|(⌊x⌋ : ℝ) + 1 - c| - |(⌊x⌋ : ℝ) - c|) *
    (Ici (1 - Int.fract x)).indicator (fun _ => (1 : ℝ)) θ

lemma gstep_eq (x c θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    |((⌊x + θ⌋ : ℤ) : ℝ) - c| = gstep x c θ := by
  rw [floor_add_eq x θ h0 h1, gstep]
  by_cases h : 1 - Int.fract x ≤ θ
  · rw [if_pos h, indicator_of_mem (show θ ∈ Ici (1 - Int.fract x) from h)]
    push_cast; ring_nf
  · rw [if_neg h, indicator_of_notMem (show θ ∉ Ici (1 - Int.fract x) from h)]
    push_cast; ring_nf

lemma ind_integrable (p : ℝ) :
    Integrable ((Ici p).indicator (fun _ => (1 : ℝ))) (volume.restrict (Ico (0 : ℝ) 1)) := by
  have : IntegrableOn (fun _ => (1 : ℝ)) (Ico (0 : ℝ) 1) volume := integrableOn_const (by simp)
  exact this.indicator measurableSet_Ici

lemma gstep_integrable (x c : ℝ) : IntegrableOn (gstep x c) (Ico 0 1) volume := by
  unfold gstep
  refine (integrableOn_const (by simp)).add ?_
  exact Integrable.const_mul (ind_integrable _) _

lemma gstep_integral (x : ℝ) (c : ℤ) :
    ∫ θ in Ico (0 : ℝ) 1, gstep x c θ = |x - c| := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  unfold gstep
  rw [integral_add (by exact integrableOn_const (by simp)), integral_const_mul,
    setIntegral_indicator measurableSet_Ici]
  · rw [setIntegral_const, setIntegral_const]
    have e1 : Ico (0 : ℝ) 1 ∩ Ici (1 - Int.fract x) = Ico (1 - Int.fract x) 1 := by
      ext y; simp only [mem_inter_iff, mem_Ico, mem_Ici]; constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨by linarith, h2⟩, h3⟩
    rw [e1]
    simp only [measureReal_def, Real.volume_Ico, smul_eq_mul, mul_one]
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
    have hx : x = ⌊x⌋ + Int.fract x := (Int.floor_add_fract x).symm
    rcases le_or_gt c ⌊x⌋ with h | h
    · have h' : (c : ℝ) ≤ ⌊x⌋ := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      ring_nf; linarith
    · have h' : (⌊x⌋ : ℝ) + 1 ≤ c := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      ring_nf; linarith
  · exact Integrable.const_mul (ind_integrable _) _

/-- Randomized rounding with a common offset: some `θ ∈ [0,1)` rounds every coordinate without
increasing `∑ |x_i - c_i|`. -/
lemma exists_offset {N : ℕ} (x : Fin N → ℝ) (c : Fin N → ℤ) :
    ∃ θ ∈ Ico (0 : ℝ) 1, ∑ i, |((⌊x i + θ⌋ : ℤ) : ℝ) - c i| ≤ ∑ i, |x i - c i| := by
  have hint : IntegrableOn (fun θ => ∑ i, gstep (x i) (c i) θ) (Ico 0 1) volume :=
    integrable_finset_sum _ (fun i _ => gstep_integrable (x i) (c i))
  have hvol : volume (Ico (0 : ℝ) 1) = 1 := by simp
  obtain ⟨θ, hθ, hle⟩ := exists_le_setAverage (by rw [hvol]; simp) (by rw [hvol]; simp) hint
  refine ⟨θ, hθ, ?_⟩
  rw [setAverage_eq, measureReal_def, hvol] at hle
  simp only [ENNReal.toReal_one, inv_one, one_smul] at hle
  rw [integral_finset_sum _ (fun i _ => gstep_integrable (x i) (c i))] at hle
  simp only [gstep_integral] at hle
  have : ∑ i, |((⌊x i + θ⌋ : ℤ) : ℝ) - c i| = ∑ i, gstep (x i) (c i) θ :=
    Finset.sum_congr rfl (fun i _ => gstep_eq _ _ _ hθ.1 hθ.2)
  rw [this]; exact hle

open GTWSched.NPC

/-- Integral doubled starting times exist for every feasible real schedule. -/
theorem round_schedule {N : ℕ} (l M : Fin N → ℕ) (k : ℕ) (s : Fin N → ℝ)
    (hs : IsSchedule (fun i => (l i : ℝ)) s)
    (hc : midCost (fun i => (l i : ℝ)) (fun i => (M i : ℝ)) s ≤ k) :
    ∃ t : Fin N → ℕ, (∀ i j, i ≠ j → t i + 2 * l i ≤ t j ∨ t j + 2 * l j ≤ t i) ∧
      ∑ i, ((t i : ℤ) + l i - 2 * M i).natAbs ≤ 2 * k := by
  obtain ⟨θ, hθ, hle⟩ := exists_offset (fun i => 2 * s i) (fun i => 2 * (M i : ℤ) - l i)
  have hpos : ∀ i, 0 ≤ ⌊2 * s i + θ⌋ := fun i =>
    Int.floor_nonneg.mpr (by have := hs.1 i; linarith [hθ.1])
  refine ⟨fun i => (⌊2 * s i + θ⌋).toNat, ?_, ?_⟩
  · intro i j hij
    have key : ∀ a b : Fin N, s a + l a ≤ s b →
        (⌊2 * s a + θ⌋).toNat + 2 * l a ≤ (⌊2 * s b + θ⌋).toNat := by
      intro a b hab
      have h1 : ⌊2 * s a + θ⌋ + 2 * (l a : ℤ) ≤ ⌊2 * s b + θ⌋ := by
        rw [← Int.floor_add_intCast]; apply Int.floor_mono; push_cast; linarith
      have ha := hpos a; have hb := hpos b
      omega
    rcases hs.2 i j hij with h | h
    · exact Or.inl (key i j h)
    · exact Or.inr (key j i h)
  · have hcost : ∑ i, |2 * s i - ((2 * (M i : ℤ) - l i : ℤ) : ℝ)| ≤ 2 * k := by
      have : ∑ i, |2 * s i - ((2 * (M i : ℤ) - l i : ℤ) : ℝ)| =
          2 * midCost (fun i => (l i : ℝ)) (fun i => (M i : ℝ)) s := by
        unfold midCost mid
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show 2 * s i - ((2 * (M i : ℤ) - l i : ℤ) : ℝ) = 2 * (s i + (l i : ℝ) / 2 - M i) by
          push_cast; ring, abs_mul]
        norm_num
      rw [this]; linarith
    have h2 := le_trans hle hcost
    have h3 : ((∑ i, ((((⌊2 * s i + θ⌋).toNat : ℕ) : ℤ) + l i - 2 * M i).natAbs : ℕ) : ℝ) =
        ∑ i, |((⌊2 * s i + θ⌋ : ℤ) : ℝ) - ((2 * (M i : ℤ) - l i : ℤ) : ℝ)| := by
      push_cast
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Int.toNat_of_nonneg (hpos i)]
      rw [Nat.cast_natAbs]
      push_cast
      congr 1; ring
    have : ((∑ i, ((((⌊2 * s i + θ⌋).toNat : ℕ) : ℤ) + l i - 2 * M i).natAbs : ℕ) : ℝ) ≤
        ((2 * k : ℕ) : ℝ) := by rw [h3]; push_cast at h2 ⊢; exact h2
    exact_mod_cast this

end TDNPRound



open CookPvsNP ProjSchedTW.Complexity GTWSched.NPC

namespace TDNPTop

/-! ## A polynomial-time language: the nonempty strings -/

def M1 (A : Type) : TM A where
  Q := Fin 3
  q₀ := 0
  qaccept := 1
  qreject := 2
  accept_ne_reject := by decide
  δ := fun _ s => (if s.isSome then 1 else 2, s, Move.right)

theorem step_halt {A : Type} (M : TM A) (c : Cfg A M.Q) (h : M.IsHalting c) : M.step c = c := by
  unfold TM.step
  rw [if_pos h]

theorem run_succ_eq (A : Type) (w : List A) (m : ℕ) :
    (M1 A).run (m + 1) ((M1 A).init w) = (M1 A).step ((M1 A).init w) := by
  unfold TM.run
  rw [Function.iterate_succ_apply]
  apply Function.iterate_fixed
  have hh : (M1 A).IsHalting ((M1 A).step ((M1 A).init w)) := by
    unfold TM.IsHalting
    cases w <;> simp [TM.step, TM.init, TM.IsHalting, M1]
  exact step_halt _ _ hh

theorem state_step (A : Type) (w : List A) :
    ((M1 A).step ((M1 A).init w)).state = if w = [] then (2 : Fin 3) else 1 := by
  cases w <;> simp [TM.step, TM.init, TM.IsHalting, M1]

theorem nonempty_mem_P (A : Type) [Fintype A] : {w : List A | w ≠ []} ∈ P A := by
  refine ⟨A, inferInstance, Function.Embedding.refl A, M1 A, 1, fun w => ?_, fun w => ?_⟩
  · unfold TM.HaltsWithin
    rw [run_succ_eq]
    unfold TM.IsHalting
    rw [state_step]
    simp only [List.map_eq_nil_iff]
    split_ifs <;> simp [M1]
  · simp only [Set.mem_ofPred_eq, TM.Accepts]
    constructor
    · intro hw
      refine ⟨0 + 1, ?_⟩
      rw [run_succ_eq, state_step]
      simp [hw, M1]
    · rintro ⟨n, hn⟩ hw
      subst hw
      cases n with
      | zero => simp [TM.run, TM.init, M1] at hn
      | succ m =>
        rw [run_succ_eq, state_step] at hn
        simp [M1] at hn

/-! ## Injectivity of the codes -/

lemma encInts_cons (z : ℤ) (l : List ℤ) : encInts (z :: l) = encInt z ++ encInts l := by
  simp [encInts]

def bval' : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval' l)

lemma bval'_bits (n : ℕ) : bval' (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bval']
  | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp [bval', ih]

lemma sep_split_inj : ∀ {u u' R R' : List BSym}, BSym.sep ∉ u → BSym.sep ∉ u' →
    u ++ BSym.sep :: R = u' ++ BSym.sep :: R' → u = u' ∧ R = R' := by
  intro u
  induction u with
  | nil =>
    intro u' R R' _ hu' h
    rcases u' with _ | ⟨a, u'⟩
    · simpa using h
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu'
  | cons a u ih =>
    intro u' R R' hu hu' h
    rcases u' with _ | ⟨b, u'⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := ih (fun hm => hu (List.mem_cons_of_mem _ hm))
        (fun hm => hu' (List.mem_cons_of_mem _ hm)) h.2
      exact ⟨by rw [h.1, h1], h2⟩

def digU (z : ℤ) : List BSym :=
  (if z < 0 then [BSym.minus] else []) ++
    (Nat.bits z.natAbs).map (fun b => if b then BSym.one else BSym.zero)

lemma encInt_eq_digU (z : ℤ) : encInt z = digU z ++ [BSym.sep] := by
  simp [encInt, encNat, digU]

lemma sep_not_mem_digU (z : ℤ) : BSym.sep ∉ digU z := by
  simp only [digU, List.mem_append, List.mem_map, not_or]
  constructor
  · split_ifs <;> simp
  · rintro ⟨b, -, hb⟩; cases b <;> simp at hb

lemma map_bits_inj {a b : List Bool}
    (h : a.map (fun b => if b then BSym.one else BSym.zero) =
      b.map (fun b => if b then BSym.one else BSym.zero)) : a = b := by
  refine List.map_injective_iff.mpr ?_ h
  intro x y hxy; cases x <;> cases y <;> simp_all

lemma digU_inj {z z' : ℤ} (h : digU z = digU z') : z = z' := by
  have key : ∀ {z z' : ℤ}, digU z = digU z' → (z < 0 ↔ z' < 0) := by
    intro z z' h
    by_contra hne
    simp only [digU] at h
    rcases lt_or_ge z 0 with hz | hz <;> rcases lt_or_ge z' 0 with hz' | hz'
    · exact hne (iff_of_true hz hz')
    · rw [if_pos hz, if_neg (not_lt.2 hz')] at h
      cases hb : Nat.bits z'.natAbs with
      | nil => rw [hb] at h; simp at h
      | cons c l => rw [hb] at h; cases c <;> simp at h
    · rw [if_neg (not_lt.2 hz), if_pos hz'] at h
      cases hb : Nat.bits z.natAbs with
      | nil => rw [hb] at h; simp at h
      | cons c l => rw [hb] at h; cases c <;> simp at h
    · exact hne (iff_of_false (not_lt.2 hz) (not_lt.2 hz'))
  have hs := key h
  have habs : z.natAbs = z'.natAbs := by
    simp only [digU] at h
    by_cases hz : z < 0
    · rw [if_pos hz, if_pos (hs.1 hz)] at h
      simp only [List.singleton_append, List.cons.injEq, true_and] at h
      rw [← bval'_bits z.natAbs, ← bval'_bits z'.natAbs, map_bits_inj h]
    · rw [if_neg hz, if_neg (fun h' => hz (hs.2 h'))] at h
      simp only [List.nil_append] at h
      rw [← bval'_bits z.natAbs, ← bval'_bits z'.natAbs, map_bits_inj h]
  omega

lemma encInts_inj : ∀ (l l' : List ℤ), encInts l = encInts l' → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    rcases l' with _ | ⟨z, l'⟩
    · rfl
    · rw [encInts_cons, encInt_eq_digU] at h; simp [encInts] at h
  | cons z l ih =>
    intro l' h
    rcases l' with _ | ⟨z', l'⟩
    · rw [encInts_cons, encInt_eq_digU] at h; simp [encInts] at h
    · rw [encInts_cons, encInts_cons, encInt_eq_digU, encInt_eq_digU] at h
      simp only [List.append_assoc, List.singleton_append] at h
      obtain ⟨h1, h2⟩ := sep_split_inj (sep_not_mem_digU z) (sep_not_mem_digU z') h
      rw [digU_inj h1, ih l' h2]

lemma none_split_inj {α β : Type} : ∀ {w w' : List α} {y y' : List β},
    w.map (some ∘ Sum.inl) ++ (none : Option (α ⊕ β)) :: y.map (some ∘ Sum.inr) =
      w'.map (some ∘ Sum.inl) ++ none :: y'.map (some ∘ Sum.inr) → w = w' ∧ y = y' := by
  intro w
  induction w with
  | nil =>
    intro w' y y' h
    rcases w' with _ | ⟨a, w'⟩
    · simp only [List.map_nil, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, List.map_injective_iff.2 (fun a b hab => by
        simpa using hab) h⟩
    · simp at h
  | cons a w ih =>
    intro w' y y' h
    rcases w' with _ | ⟨b, w'⟩
    · simp at h
    · simp only [List.map_cons, List.cons_append, List.cons.injEq, Function.comp_apply,
        Option.some.injEq, Sum.inl.injEq] at h
      obtain ⟨h1, h2⟩ := ih h.2
      exact ⟨by rw [h.1, h1], h2⟩

lemma encNats_eq (d : List ℕ) : encNats d = encInts (d.map (fun k : ℕ => (k : ℤ))) := by
  induction d with
  | nil => rfl
  | cons a d ih =>
    simp only [encNats, List.flatMap_cons, List.map_cons, encInts] at ih ⊢
    rw [ih]
    simp [encInt]

lemma encNats_inj {d d' : List ℕ} (h : encNats d = encNats d') : d = d' := by
  rw [encNats_eq, encNats_eq] at h
  exact (List.map_injective_iff.2 (Nat.cast_injective (R := ℤ))) (encInts_inj _ _ h)

abbrev A : Type := Option (BSym ⊕ BSym)

def Ew (c : List ℤ) (d : List ℕ) : List A :=
  (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr)

lemma Ew_ne_nil (c : List ℤ) (d : List ℕ) : Ew c d ≠ [] := by simp [Ew]

lemma Ew_inj {c c' : List ℤ} {d d' : List ℕ} (h : Ew c d = Ew c' d') : c = c' ∧ d = d' := by
  obtain ⟨h1, h2⟩ := none_split_inj h
  exact ⟨encInts_inj _ _ h1, encNats_inj h2⟩

/-! ## The certificate conditions -/

/-- Conditions checked by the length filter. -/
def Glen (c : List ℤ) (d : List ℕ) : Prop :=
  (∀ v ∈ c, 0 < v) ∧ c.length = 2 + 2 * (c.getD 0 0).toNat ∧
    d.length = 3 * (c.getD 0 0).toNat + 1

/-- Conditions checked by the cost filter. -/
def Gcost (c : List ℤ) (d : List ℕ) : Prop :=
  d.getD 0 0 = 0 ∧
    (∀ i < d.length / 3,
      d.getD (3 * i + 1) 0 + (c.getD (2 + d.length / 3 + i) 0).natAbs = d.getD (3 * i + 2) 0 ∧
      d.getD (3 * i + 2) 0 + d.getD (3 * i) 0 ≤
        2 * (c.getD (2 + i) 0).natAbs + d.getD (3 * i + 3) 0 ∧
      2 * (c.getD (2 + i) 0).natAbs + d.getD (3 * i) 0 ≤
        d.getD (3 * i + 2) 0 + d.getD (3 * i + 3) 0) ∧
    d.getD (3 * (d.length / 3)) 0 ≤ 2 * (c.getD 1 0).natAbs

/-- Conditions checked by the overlap filter. -/
def Govl (c : List ℤ) (d : List ℕ) : Prop :=
  ∀ i < d.length / 3, ∀ j < d.length / 3, i < j →
    d.getD (3 * i + 1) 0 + 2 * (c.getD (2 + d.length / 3 + i) 0).natAbs ≤ d.getD (3 * j + 1) 0 ∨
      d.getD (3 * j + 1) 0 + 2 * (c.getD (2 + d.length / 3 + j) 0).natAbs ≤ d.getD (3 * i + 1) 0

def Good (c : List ℤ) (d : List ℕ) : Prop := Glen c d ∧ Gcost c d ∧ Govl c d

/-- The checking relation: `w` is the code of the number list `c` and `y` the code of the
certificate `d`. -/
def Rchk (w y : List BSym) : Prop :=
  ∃ c : List ℤ, ∃ d : List ℕ, w = encInts c ∧ y = encNats d ∧ Good c d

lemma checkLang_iff (u : List A) : u ∈ checkLang Rchk ↔ ∃ c d, u = Ew c d ∧ Good c d := by
  constructor
  · rintro ⟨w, y, ⟨c, d, rfl, rfl, hg⟩, rfl⟩
    exact ⟨c, d, rfl, hg⟩
  · rintro ⟨c, d, rfl, hg⟩
    exact ⟨encInts c, encNats d, ⟨c, d, rfl, rfl, hg⟩, rfl⟩

/-! ## Polynomial-time decision of the checking language -/

open Classical in
noncomputable def filt (P : List A → Prop) (u : List A) : List A := if P u then u else []

lemma filt_filt (P Q : List A → Prop) (u : List A) :
    filt P (filt Q u) = filt (fun v => Q v ∧ P v) u := by
  unfold filt
  by_cases hQ : Q u <;> by_cases hP : P u <;> simp [hQ, hP]

lemma ptc_of_exec {P : List A → Prop}
    (h : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (p : StackProg K A) (ki ko : K) (k : ℕ),
      ∀ u : List A, ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
        s ko = filt P u) : PolyTimeComputable (filt P) := by
  classical
  obtain ⟨K, _, _, p, ki, ko, k, hp⟩ := h
  exact CookPvsNP.stack_program_polytime p ki ko _ k hp

lemma ptc_kill (Q : List A → Prop)
    (h : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (p : StackProg K A) (ki ko : K) (k : ℕ),
      ∀ u : List A, ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
        (Q u → s ko = []) ∧ (¬Q u → s ko = u)) : PolyTimeComputable (filt (fun u => ¬Q u)) := by
  apply ptc_of_exec
  obtain ⟨K, i1, i2, p, ki, ko, k, hp⟩ := h
  refine ⟨K, i1, i2, p, ki, ko, k, fun u => ?_⟩
  obtain ⟨s, n, h1, h2, h3, h4⟩ := hp u
  refine ⟨s, n, h1, h2, ?_⟩
  unfold filt
  by_cases hq : Q u
  · rw [if_neg (not_not.mpr hq)]; exact h3 hq
  · rw [if_pos hq]; exact h4 hq

lemma ptc_keep (Q : List A → Prop)
    (h : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (p : StackProg K A) (ki ko : K) (k : ℕ),
      ∀ u : List A, ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
        (Q u → s ko = u) ∧ (¬Q u → s ko = [])) : PolyTimeComputable (filt Q) := by
  apply ptc_of_exec
  obtain ⟨K, i1, i2, p, ki, ko, k, hp⟩ := h
  refine ⟨K, i1, i2, p, ki, ko, k, fun u => ?_⟩
  obtain ⟨s, n, h1, h2, h3, h4⟩ := hp u
  refine ⟨s, n, h1, h2, ?_⟩
  unfold filt
  by_cases hq : Q u
  · rw [if_pos hq]; exact h3 hq
  · rw [if_neg hq]; exact h4 hq

def Plen (u : List A) : Prop := ∃ c d, u = Ew c d ∧ Glen c d
def Qcost (u : List A) : Prop := ∃ c d, u = Ew c d ∧ ¬Gcost c d
def Qovl (u : List A) : Prop := ∃ c d, u = Ew c d ∧ ¬Govl c d

lemma ptc_len : PolyTimeComputable (filt Plen) :=
  ptc_keep Plen tdCheck_len_filter
lemma ptc_cost : PolyTimeComputable (filt (fun u => ¬Qcost u)) :=
  ptc_kill Qcost tdCheck_cost_filter
lemma ptc_ovl : PolyTimeComputable (filt (fun u => ¬Qovl u)) :=
  ptc_kill Qovl tdCheck_overlap_filter

lemma conj_iff (u : List A) :
    (∃ c d, u = Ew c d ∧ Good c d) ↔ Plen u ∧ ¬Qcost u ∧ ¬Qovl u := by
  constructor
  · rintro ⟨c, d, rfl, hl, hc, ho⟩
    refine ⟨⟨c, d, rfl, hl⟩, ?_, ?_⟩
    · rintro ⟨c', d', he, hn⟩; obtain ⟨rfl, rfl⟩ := Ew_inj he; exact hn hc
    · rintro ⟨c', d', he, hn⟩; obtain ⟨rfl, rfl⟩ := Ew_inj he; exact hn ho
  · rintro ⟨⟨c, d, rfl, hl⟩, hc, ho⟩
    refine ⟨c, d, rfl, hl, ?_, ?_⟩
    · by_contra hn; exact hc ⟨c, d, rfl, hn⟩
    · by_contra hn; exact ho ⟨c, d, rfl, hn⟩

theorem checker_ptc : ∃ f : List A → List A, PolyTimeComputable f ∧
    ∀ u, u ∈ checkLang Rchk ↔ f u ≠ [] := by
  classical
  refine ⟨_, CookPvsNP.polyTimeComputable_comp _ _
    (CookPvsNP.polyTimeComputable_comp _ _ ptc_len ptc_cost) ptc_ovl, fun u => ?_⟩
  simp only [Function.comp_apply, filt_filt]
  rw [checkLang_iff, conj_iff]
  unfold filt
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [if_pos ⟨⟨h1, h2⟩, h3⟩]
    obtain ⟨c, d, rfl, -⟩ := h1
    exact Ew_ne_nil c d
  · intro h
    by_cases hc : (Plen u ∧ ¬Qcost u) ∧ ¬Qovl u
    · exact ⟨hc.1.1, hc.1.2, hc.2⟩
    · rw [if_neg hc] at h; exact absurd rfl h

/-! ## Size bounds -/

lemma len_encNat (v : ℕ) : (encNat v).length = v.size + 1 := by
  simp [encNat, Nat.size_eq_bits_len]

lemma len_encInts (l : List ℤ) :
    (l.map fun z => z.natAbs.size + 1).sum ≤ (encInts l).length := by
  induction l with
  | nil => simp [encInts]
  | cons a l ih =>
    simp only [encInts, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons] at ih ⊢
    have : a.natAbs.size + 1 ≤ (encInt a).length := by
      simp only [encInt, List.length_append, len_encNat]; omega
    omega

lemma length_le_sum (l : List ℤ) : l.length ≤ (l.map fun z => z.natAbs.size + 1).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

lemma one_add_sum_le (l : List ℤ) :
    1 + (l.map Int.natAbs).sum ≤ 2 ^ (l.map fun z => z.natAbs.size + 1).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : a.natAbs < 2 ^ a.natAbs.size := Nat.lt_size_self _
    rw [pow_add, pow_add, pow_one]
    generalize 2 ^ (l.map fun z => z.natAbs.size + 1).sum = F at ih ⊢
    generalize 2 ^ a.natAbs.size = P at h1 ⊢
    have hF : 1 ≤ F := by omega
    have hP : 1 ≤ P := by omega
    have e1 : P ≤ P * F := Nat.le_mul_of_pos_right _ hF
    have e2 : F ≤ P * F := Nat.le_mul_of_pos_left _ hP
    nlinarith [e1, e2]

lemma len_encNats_le (B : ℕ) (xs : List ℕ) (h : ∀ v ∈ xs, v < 2 ^ B) :
    (encNats xs).length ≤ xs.length * (B + 1) := by
  induction xs with
  | nil => simp [encNats]
  | cons a l ih =>
    simp only [encNats, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have ha : a.size ≤ B := Nat.size_le.2 (h a (by simp))
    have := ih (fun v hv => h v (by simp [hv]))
    rw [len_encNat]; nlinarith

lemma natAbs_le_sum (l : List ℤ) (z : ℤ) (hz : z ∈ l) : z.natAbs ≤ (l.map Int.natAbs).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem hz)

/-! ## The instance list of a code -/

/-- The number list of `tdCode N k M l`. -/
def instL {N : ℕ} (k : ℕ) (M l : Fin N → ℕ) : List ℕ := N :: k :: (List.ofFn M ++ List.ofFn l)

lemma instL_length {N : ℕ} (k : ℕ) (M l : Fin N → ℕ) : (instL k M l).length = 2 + 2 * N := by
  simp [instL]; omega

lemma instL_getD_M {N : ℕ} (k : ℕ) (M l : Fin N → ℕ) (i : ℕ) (hi : i < N) :
    (instL k M l).getD (2 + i) 0 = M ⟨i, hi⟩ := by
  rw [show 2 + i = i + 1 + 1 by omega]
  simp only [instL, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  have : i < (List.ofFn M).length := by simpa using hi
  rw [List.getElem?_append_left this]; simp [hi]

lemma instL_getD_l {N : ℕ} (k : ℕ) (M l : Fin N → ℕ) (i : ℕ) (hi : i < N) :
    (instL k M l).getD (2 + N + i) 0 = l ⟨i, hi⟩ := by
  rw [show 2 + N + i = (N + i) + 1 + 1 by omega]
  simp only [instL, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]
  simp [hi]

/-! ## Certificates from schedules and schedules from certificates -/

/-- The certificate list built from doubled starting times `t`. -/
def certL {N : ℕ} (l M : Fin N → ℕ) (t : Fin N → ℕ) : List ℕ :=
  let t' : ℕ → ℕ := fun i => if h : i < N then t ⟨i, h⟩ else 0
  let l' : ℕ → ℕ := fun i => if h : i < N then l ⟨i, h⟩ else 0
  let a : ℕ → ℕ := fun i => if h : i < N then ((t ⟨i, h⟩ : ℤ) + l ⟨i, h⟩ - 2 * M ⟨i, h⟩).natAbs
    else 0
  (List.range (3 * N + 1)).map fun q =>
    if q % 3 = 0 then ∑ j ∈ Finset.range (q / 3), a j
    else if q % 3 = 1 then t' (q / 3) else t' (q / 3) + l' (q / 3)

lemma certL_length {N : ℕ} (l M t : Fin N → ℕ) : (certL l M t).length = 3 * N + 1 := by
  simp [certL]

lemma certL_getD {N : ℕ} (l M t : Fin N → ℕ) (q : ℕ) (hq : q < 3 * N + 1) :
    (certL l M t).getD q 0 =
      if q % 3 = 0 then ∑ j ∈ Finset.range (q / 3),
          (if h : j < N then ((t ⟨j, h⟩ : ℤ) + l ⟨j, h⟩ - 2 * M ⟨j, h⟩).natAbs else 0)
      else if q % 3 = 1 then (if h : q / 3 < N then t ⟨q / 3, h⟩ else 0)
      else (if h : q / 3 < N then t ⟨q / 3, h⟩ else 0) +
        (if h : q / 3 < N then l ⟨q / 3, h⟩ else 0) := by
  simp [certL, List.getD_eq_getElem?_getD, hq]

lemma certL_P {N : ℕ} (l M t : Fin N → ℕ) (i : ℕ) (hi : i ≤ N) :
    (certL l M t).getD (3 * i) 0 = ∑ j ∈ Finset.range i,
      (if h : j < N then ((t ⟨j, h⟩ : ℤ) + l ⟨j, h⟩ - 2 * M ⟨j, h⟩).natAbs else 0) := by
  rw [certL_getD l M t _ (by omega)]
  simp [show 3 * i / 3 = i by omega]

lemma certL_t {N : ℕ} (l M t : Fin N → ℕ) (i : ℕ) (hi : i < N) :
    (certL l M t).getD (3 * i + 1) 0 = t ⟨i, hi⟩ := by
  rw [certL_getD l M t _ (by omega)]
  simp [show (3 * i + 1) % 3 = 1 by omega, show (3 * i + 1) / 3 = i by omega, hi]

lemma certL_h {N : ℕ} (l M t : Fin N → ℕ) (i : ℕ) (hi : i < N) :
    (certL l M t).getD (3 * i + 2) 0 = t ⟨i, hi⟩ + l ⟨i, hi⟩ := by
  rw [certL_getD l M t _ (by omega)]
  simp [show (3 * i + 2) % 3 = 2 by omega, show (3 * i + 2) / 3 = i by omega, hi]

lemma natAbs_sub_le (h m : ℕ) : h ≤ 2 * m + ((h : ℤ) - 2 * m).natAbs ∧
    2 * m ≤ h + ((h : ℤ) - 2 * m).natAbs := by omega

/-- Direction `⇒`: a yes-instance has a short certificate. -/
theorem cert_of_yes {N : ℕ} (k : ℕ) (M l : Fin N → ℕ) (hN : 0 < N) (hk : 0 < k)
    (hM : ∀ i, 0 < M i) (hl : ∀ i, 0 < l i)
    (hY : TDYesReal (fun i => (l i : ℝ)) (fun i => (M i : ℝ)) (k : ℝ)) :
    ∃ y : List BSym, y.length ≤ (tdCode N k M l).length ^ 4 ∧ Rchk (tdCode N k M l) y := by
  obtain ⟨s, hs, hcost⟩ := hY
  obtain ⟨t, hovl, hsum⟩ := TDNPRound.round_schedule l M k s hs hcost
  set c : List ℤ := (instL k M l).map (fun v : ℕ => (v : ℤ)) with hc
  set d := certL l M t with hd
  have hw : tdCode N k M l = encInts c := by
    rw [hc, ← encNats_eq]; rfl
  have hcl : c.length = 2 + 2 * N := by simp [hc, instL_length]
  have hc0 : c.getD 0 0 = N := by simp [hc, instL]
  have hc1 : c.getD 1 0 = k := by simp [hc, instL]
  have hcM : ∀ i (hi : i < N), c.getD (2 + i) 0 = M ⟨i, hi⟩ := by
    intro i hi
    have := instL_getD_M k M l i hi
    simp only [hc, List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
    rw [← this]; cases (instL k M l)[2 + i]? <;> simp
  have hcl' : ∀ i (hi : i < N), c.getD (2 + N + i) 0 = l ⟨i, hi⟩ := by
    intro i hi
    have := instL_getD_l k M l i hi
    simp only [hc, List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
    rw [← this]; cases (instL k M l)[2 + N + i]? <;> simp
  have hdl : d.length = 3 * N + 1 := certL_length l M t
  have hd3 : d.length / 3 = N := by omega
  -- the sum of the cost terms over `range N`
  set a : ℕ → ℕ := fun j => if h : j < N then ((t ⟨j, h⟩ : ℤ) + l ⟨j, h⟩ - 2 * M ⟨j, h⟩).natAbs
    else 0 with ha
  have hsumN : ∑ j ∈ Finset.range N, a j ≤ 2 * k := by
    have : ∑ j ∈ Finset.range N, a j = ∑ i : Fin N, ((t i : ℤ) + l i - 2 * M i).natAbs := by
      rw [Finset.sum_range (fun j => a j)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [ha, i.isLt]
    rw [this]; exact hsum
  have hgood : Good c d := by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro v hv
      simp only [hc, List.mem_map] at hv
      obtain ⟨x, hx, rfl⟩ := hv
      simp only [instL, List.mem_cons, List.mem_append, List.mem_ofFn] at hx
      rcases hx with rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact_mod_cast hN
      · exact_mod_cast hk
      · exact_mod_cast hM i
      · exact_mod_cast hl i
    · rw [hcl, hc0]; simp
    · rw [hdl, hc0]; simp
    · have := certL_P l M t 0 (Nat.zero_le _)
      simpa using this
    · intro i hi
      rw [hd3] at hi ⊢
      rw [hcl' i hi, hcM i hi, certL_t l M t i hi, certL_h l M t i hi,
        show 3 * i + 3 = 3 * (i + 1) by ring, certL_P l M t i (by omega),
        certL_P l M t (i + 1) (by omega), Finset.sum_range_succ]
      rw [dif_pos hi]
      have hz := natAbs_sub_le (t ⟨i, hi⟩ + l ⟨i, hi⟩) (M ⟨i, hi⟩)
      push_cast at hz
      generalize ((t ⟨i, hi⟩ : ℤ) + l ⟨i, hi⟩ - 2 * M ⟨i, hi⟩).natAbs = z at hz ⊢
      generalize (Finset.range i).sum a = Q
      simp only [Int.natAbs_natCast]
      refine ⟨?_, ?_, ?_⟩ <;> first | trivial | omega
    · rw [hd3, certL_P l M t N le_rfl, hc1]
      simpa [← ha] using hsumN
    · intro i hi j hj hij
      rw [hd3] at hi hj ⊢
      rw [hcl' i hi, hcl' j hj, certL_t l M t i hi, certL_t l M t j hj]
      simp only [Int.natAbs_natCast]
      exact hovl ⟨i, hi⟩ ⟨j, hj⟩ (fun h => by
        have := congrArg Fin.val h; simp at this; omega)
  refine ⟨encNats d, ?_, c, d, hw, rfl, hgood⟩
  -- size bound
  rw [hw]
  set L := (encInts c).length with hL
  have hsz := len_encInts c
  have hpow := one_add_sum_le c
  have hlen := length_le_sum c
  set S := (c.map Int.natAbs).sum with hS
  have hSL : 1 + S ≤ 2 ^ L := le_trans hpow (Nat.pow_le_pow_right (by norm_num) hsz)
  have hNL : 2 + 2 * N ≤ L := by omega
  have hmemS : ∀ z ∈ c, z.natAbs ≤ S := fun z hz => natAbs_le_sum c z hz
  have hMS : ∀ i (hi : i < N), M ⟨i, hi⟩ ≤ S := by
    intro i hi
    have := hmemS (c.getD (2 + i) 0) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; simp)
    rw [hcM i hi] at this; simpa using this
  have hlS : ∀ i (hi : i < N), l ⟨i, hi⟩ ≤ S := by
    intro i hi
    have := hmemS (c.getD (2 + N + i) 0) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; simp)
    rw [hcl' i hi] at this; simpa using this
  have hkS : k ≤ S := by
    have := hmemS (c.getD 1 0) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; simp)
    rw [hc1] at this; simpa using this
  have hL2 : 2 ≤ L := by omega
  have h4 : 4 * 2 ^ L ≤ 2 ^ (2 * L) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul_right _ (by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL2)
  have hai : ∀ i (hi : i < N), a i ≤ 2 * k := by
    intro i hi
    calc a i ≤ ∑ j ∈ Finset.range N, a j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)
      _ ≤ 2 * k := hsumN
  have hB : ∀ v ∈ d, v < 2 ^ (2 * L) := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hv
    have hq' : q < 3 * N + 1 := by rw [← hdl]; exact hq
    have hv' : d[q] = d.getD q 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; simp
    rw [hv']
    have hbound : d.getD q 0 ≤ 4 * S := by
      rw [hd, certL_getD l M t q hq']
      split_ifs with h1 h2 h3 h4' h5 h6
      · have hq3 : q / 3 ≤ N := by omega
        calc (∑ j ∈ Finset.range (q / 3), a j) ≤ ∑ j ∈ Finset.range N, a j :=
              Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hq3)
          _ ≤ 2 * k := hsumN
          _ ≤ 4 * S := by omega
      all_goals first
        | (have e := hai (q / 3) (by assumption)
           have e2 := hMS (q / 3) (by assumption)
           have e3 := hlS (q / 3) (by assumption)
           simp only [ha, dif_pos (show q / 3 < N by assumption)] at e
           omega)
        | omega
    omega
  have hy := len_encNats_le (2 * L) d hB
  rw [hdl] at hy
  have hL4 : (3 * N + 1) * (2 * L + 1) ≤ L ^ 4 := by
    have hL3 : 3 ≤ L := by omega
    have h44 : L ^ 4 = (L * L) * (L * L) := by ring
    rw [h44]
    have h5 : (3 * N + 1) * (2 * L + 1) ≤ (2 * L) * (2 * L + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have hA : 9 ≤ L * L := Nat.mul_le_mul hL3 hL3
    have hB2 : 9 * (L * L) ≤ (L * L) * (L * L) := Nat.mul_le_mul_right _ hA
    have hC : L ≤ L * L := Nat.le_mul_self L
    nlinarith [hA, hB2, hC]
  omega

lemma toNat_cast_of_pos {z : ℤ} (h : 0 < z) : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h.le

lemma getD_mem {c : List ℤ} {q : ℕ} (hq : q < c.length) : c.getD q 0 ∈ c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; simp

lemma list_ext_getD {L1 L2 : List ℕ} (hl : L1.length = L2.length)
    (h : ∀ q < L1.length, L1.getD q 0 = L2.getD q 0) : L1 = L2 := by
  apply List.ext_getElem hl
  intro q h1 h2
  have := h q h1
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

/-- Direction `⇐`: a certificate yields a schedule of cost at most `k`. -/
theorem yes_of_cert (w y : List BSym) (h : Rchk w y) : w ∈ tdLang := by
  obtain ⟨c, d, rfl, rfl, ⟨hpos, hcl, hdl⟩, ⟨hd0, hcost, hfin⟩, hovl⟩ := h
  simp only [Govl] at hovl
  set N := (c.getD 0 0).toNat with hN
  have hd3 : d.length / 3 = N := by omega
  rw [hd3] at hcost hfin hovl
  have hpos' : ∀ q, q < c.length → 0 < c.getD q 0 := fun q hq => hpos _ (getD_mem hq)
  set k := (c.getD 1 0).toNat with hk
  set M : Fin N → ℕ := fun i => (c.getD (2 + i) 0).toNat with hM
  set l : Fin N → ℕ := fun i => (c.getD (2 + N + i) 0).toNat with hl
  have hcast : ∀ q, q < c.length → (((c.getD q 0).toNat : ℕ) : ℤ) = c.getD q 0 :=
    fun q hq => toNat_cast_of_pos (hpos' q hq)
  have habs : ∀ q, q < c.length → (c.getD q 0).natAbs = (c.getD q 0).toNat := by
    intro q hq; have := hpos' q hq; omega
  have hNpos : 0 < N := by have := hpos' 0 (by omega); omega
  -- the code
  have hinst : instL k M l = c.map Int.toNat := by
    apply list_ext_getD (by simp [instL_length, hcl])
    intro q hq
    rw [instL_length] at hq
    have hq' : q < c.length := by omega
    have e2 : (c.map Int.toNat).getD q 0 = (c.getD q 0).toNat := by
      simp [List.getD_eq_getElem?_getD, hq']
    rw [e2]
    rcases Nat.lt_or_ge q 2 with h2 | h2
    · interval_cases q
      · simp [instL, hN]
      · simp [instL, hk]
    · rcases Nat.lt_or_ge q (2 + N) with h3 | h3
      · obtain ⟨i, rfl⟩ : ∃ i, q = 2 + i := ⟨q - 2, by omega⟩
        rw [instL_getD_M k M l i (by omega)]
      · obtain ⟨i, rfl⟩ : ∃ i, q = 2 + N + i := ⟨q - 2 - N, by omega⟩
        rw [instL_getD_l k M l i (by omega)]
  have hcode : encInts c = tdCode N k M l := by
    have : c = (instL k M l).map (fun v : ℕ => (v : ℤ)) := by
      rw [hinst, List.map_map]
      apply List.ext_getElem (by simp)
      intro q h1 h2
      simp only [List.getElem_map, Function.comp_apply]
      have := hcast q h1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at this
      simpa using this.symm
    rw [this, ← encNats_eq]; rfl
  refine ⟨N, k, M, l, hNpos, ?_, ?_, ?_, ?_, hcode⟩
  · have := hpos' 1 (by omega); omega
  · intro i; have := hpos' (2 + i) (by have := i.isLt; omega); simp only [hM]; omega
  · intro i; have := hpos' (2 + N + i) (by have := i.isLt; omega); simp only [hl]; omega
  -- the schedule
  set t : ℕ → ℕ := fun i => d.getD (3 * i + 1) 0 with ht
  refine ⟨fun i => (t i : ℝ) / 2, ⟨fun i => by positivity, ?_⟩, ?_⟩
  · intro i j hij
    have key : ∀ a b : Fin N, t a + 2 * l a ≤ t b →
        (t a : ℝ) / 2 + (l a : ℝ) ≤ (t b : ℝ) / 2 := by
      intro a b hab
      have : (t a : ℝ) + 2 * (l a : ℝ) ≤ t b := by exact_mod_cast hab
      linarith
    have hla : ∀ a : Fin N, (c.getD (2 + N + a) 0).natAbs = l a := fun a =>
      habs _ (by have := a.isLt; omega)
    rcases Nat.lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with h | h
    · rcases hovl i i.isLt j j.isLt h with h' | h'
      · left; apply key; rw [← hla i]; exact h'
      · right; apply key; rw [← hla j]; exact h'
    · rcases hovl j j.isLt i i.isLt h with h' | h'
      · right; apply key; rw [← hla j]; exact h'
      · left; apply key; rw [← hla i]; exact h'
  · unfold midCost mid
    have hterm : ∀ i : Fin N, |(t i : ℝ) / 2 + (l i : ℝ) / 2 - (M i : ℝ)| ≤
        ((d.getD (3 * (i : ℕ) + 3) 0 : ℝ) - d.getD (3 * (i : ℕ)) 0) / 2 := by
      intro i
      obtain ⟨e1, e2, e3⟩ := hcost i i.isLt
      rw [habs _ (by have := i.isLt; omega)] at e1
      rw [habs _ (by have := i.isLt; omega)] at e2 e3
      have e1' : (t i : ℝ) + (l i : ℝ) = d.getD (3 * (i : ℕ) + 2) 0 := by
        simp only [ht, hl]; exact_mod_cast e1
      have e2' : (d.getD (3 * (i : ℕ) + 2) 0 : ℝ) + d.getD (3 * (i : ℕ)) 0 ≤
          2 * (M i : ℝ) + d.getD (3 * (i : ℕ) + 3) 0 := by simp only [hM]; exact_mod_cast e2
      have e3' : 2 * (M i : ℝ) + d.getD (3 * (i : ℕ)) 0 ≤
          d.getD (3 * (i : ℕ) + 2) 0 + d.getD (3 * (i : ℕ) + 3) 0 := by
        simp only [hM]; exact_mod_cast e3
      rw [abs_le]; constructor <;> linarith
    calc ∑ i : Fin N, |(t i : ℝ) / 2 + (l i : ℝ) / 2 - (M i : ℝ)|
        ≤ ∑ i : Fin N, ((d.getD (3 * (i : ℕ) + 3) 0 : ℝ) - d.getD (3 * (i : ℕ)) 0) / 2 :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = ((d.getD (3 * N) 0 : ℝ) - d.getD 0 0) / 2 := by
          rw [← Finset.sum_div]
          congr 1
          rw [Finset.sum_fin_eq_sum_range]
          rw [show (d.getD (3 * N) 0 : ℝ) - d.getD 0 0 = ∑ i ∈ Finset.range N,
              ((d.getD (3 * (i + 1)) 0 : ℝ) - d.getD (3 * i) 0) by
            rw [Finset.sum_range_sub (fun i => (d.getD (3 * i) 0 : ℝ))]]
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [dif_pos (Finset.mem_range.1 hi)]
          simp only [show 3 * (i + 1) = 3 * i + 3 by ring]
      _ ≤ (k : ℝ) := by
          rw [hd0]
          have : d.getD (3 * N) 0 ≤ 2 * k := by
            rw [hk, ← habs 1 (by omega)]; exact hfin
          have : (d.getD (3 * N) 0 : ℝ) ≤ 2 * k := by exact_mod_cast this
          push_cast; linarith

theorem td_certificate : ∀ w : List BSym,
    w ∈ tdLang ↔ ∃ y : List BSym, y.length ≤ w.length ^ 4 ∧ Rchk w y := by
  intro w
  constructor
  · rintro ⟨N, k, M, l, hN, hk, hM, hl, hY, rfl⟩
    exact cert_of_yes k M l hN hk hM hl hY
  · rintro ⟨y, -, hR⟩
    exact yes_of_cert w y hR

theorem td_mem_NP' : tdLang ∈ NP BSym := by
  classical
  obtain ⟨f, hf, hfu⟩ := checker_ptc
  refine ⟨BSym, inferInstance, inferInstance, Rchk, 4, ?_, td_certificate⟩
  exact CookPvsNP.mem_P_of_polyReducible _ {w : List A | w ≠ []} ⟨f, hf, fun u => hfu u⟩
    (nonempty_mem_P _)

end TDNPTop

theorem solution : GTWSched.NPC.tdLang ∈ CookPvsNP.NP ProjSchedTW.Complexity.BSym :=
  TDNPTop.td_mem_NP'
