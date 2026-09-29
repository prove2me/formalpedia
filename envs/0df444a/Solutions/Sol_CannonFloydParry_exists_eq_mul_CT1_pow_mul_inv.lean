-- Prove2me | solution 1 for CannonFloydParry.exists_eq_mul_CT1_pow_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T20:14:46.978688+00:00
-- url     : https://prove2.me/submissions/acce8650-f2a2-489c-bcfe-b2898bf60eb8

import Definitions.Def_CannonFloydParry_T
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib
import Theorems.Thm_CannonFloydParry_CT1_pow_relations
import Theorems.Thm_CannonFloydParry_exists_mulEquiv_F1_F
import Theorems.Thm_CannonFloydParry_existsUnique_normalForm

/-! The algebra of `T₁` (CFP pp. 236–238): relations, the map `F₁ → T₁`, `XₙXₖ = XₖXₙ₊₁`,
Lemma 5.5 and Lemma 5.6. -/

namespace CannonFloydParry.S5

open PresentedGroup

local notation "a" => (PresentedGroup.of FormalABC.A : T1)
local notation "b" => (PresentedGroup.of FormalABC.B : T1)
local notation "c" => (PresentedGroup.of FormalABC.C : T1)

lemma mem_rels {r : FreeGroup FormalABC} (h : r ∈ relsT1) : (PresentedGroup.mk relsT1 r) = 1 :=
  PresentedGroup.one_of_mem h

lemma rel1 : (a * b⁻¹) * (a⁻¹ * b * a) * (a * b⁻¹)⁻¹ * (a⁻¹ * b * a)⁻¹ = 1 := by
  have h := mem_rels (r := _) (Or.inl rfl)
  simp only [map_mul, map_inv] at h
  exact h

lemma rel2 : (a * b⁻¹) * (a⁻¹ ^ 2 * b * a ^ 2) * (a * b⁻¹)⁻¹ * (a⁻¹ ^ 2 * b * a ^ 2)⁻¹ = 1 := by
  have h := mem_rels (r := _) (Or.inr (Or.inl rfl))
  simp only [map_mul, map_inv, map_pow] at h
  exact h

lemma rel6 : c ^ 3 = 1 := by
  have h := mem_rels (r := _) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  simp only [map_pow] at h
  exact h

/-- The map `F₁ → T₁`, `A ↦ A`, `B ↦ B`. -/
noncomputable def fromF1 : F1 →* T1 :=
  PresentedGroup.toGroup (f := fun s => match s with | FormalAB.A => a | FormalAB.B => b) (by
    intro r hr
    rcases hr with rfl | rfl
    · simpa using rel1
    · simpa using rel2)

@[simp] lemma fromF1_A : fromF1 (PresentedGroup.of FormalAB.A) = a := PresentedGroup.toGroup.of _
@[simp] lemma fromF1_B : fromF1 (PresentedGroup.of FormalAB.B) = b := PresentedGroup.toGroup.of _

lemma fromF1_Y (n : ℕ) : fromF1 (Y n) = XT1 n := by
  cases n <;> simp [Y, XT1, map_mul, map_inv, map_pow]
lemma XT1_one : XT1 1 = b := by simp [XT1]
lemma CT1_one : CT1 1 = c := by simp [CT1]


section Lemma56
variable (n : ℕ) (hn : 0 < n)
include hn

end Lemma56

end CannonFloydParry.S5

/-! Theorem 5.7: every `g ∈ T₁` is `p Cₙᵐ q⁻¹` with `p`, `q` positive and `m < n + 2`.

The set `H` of such elements contains `1` and is closed under right multiplication by
`A^{±1}`, `B^{±1}`, `C^{±1}`; since these generate `T₁`, `H = T₁`. The steps are CFP's: the
normal form of `F` (Corollary 2.7, through Theorem 3.4 and `F₁ → T₁`) rewrites `q⁻¹ Xᵢ` as
`p' q'⁻¹`; Lemma 5.6 i)/iii) push positive words left through powers of `Cₙ`, ii)/iv) push
negative words right; and two powers of `C` combine as in the first paragraph of p. 239. -/

namespace CannonFloydParry.S5

local notation "genC" => (PresentedGroup.of FormalABC.C : T1)

/-- The positive word `X_{l₀} X_{l₁} ⋯`. -/
noncomputable def P (l : List ℕ) : T1 := (l.map XT1).prod

@[simp] lemma P_nil : P [] = 1 := rfl
lemma P_cons (r : ℕ) (l : List ℕ) : P (r :: l) = XT1 r * P l := by simp [P]
lemma P_append (l₁ l₂ : List ℕ) : P (l₁ ++ l₂) = P l₁ * P l₂ := by simp [P]
lemma P_replicate (c i : ℕ) : P (List.replicate c i) = XT1 i ^ c := by
  simp [P, List.map_replicate, List.prod_replicate]

lemma isPositive_P (l : List ℕ) : IsPositiveT1 (P l) := by
  unfold IsPositiveT1 P
  apply Submonoid.list_prod_mem
  intro x hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
  exact Submonoid.subset_closure ⟨r, rfl⟩

/-! ### Lemma 5.6, conjunct by conjunct -/

section
variable {n m r s : ℕ} (hn : 0 < n) (hm : 1 ≤ m) (hmn : m ≤ n + 1)
include hn hm hmn

lemma i1 (hr : r ≤ n) (h : m ≤ r) : CT1 n ^ m * XT1 r = XT1 (r - m) * CT1 (n + 1) ^ m :=
  (CT1_pow_relations n m r 0 hn hm hmn hr (Nat.zero_le _)).1 h
lemma i2 (hr : r ≤ n) (h : r + 1 = m) : CT1 n ^ m * XT1 r = CT1 (n + 1) ^ (m + 1) :=
  (CT1_pow_relations n m r 0 hn hm hmn hr (Nat.zero_le _)).2.1 h
lemma i3 (hr : r ≤ n) (h : r + 1 < m) :
    CT1 n ^ m * XT1 r = XT1 (r + (n + 2 - m)) * CT1 (n + 1) ^ (m + 1) :=
  (CT1_pow_relations n m r 0 hn hm hmn hr (Nat.zero_le _)).2.2.1 h
lemma ii1 (hs : s ≤ n) (h : n + 2 ≤ s + m) :
    (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ (m + 1) * (XT1 (s + m - (n + 2)))⁻¹ :=
  (CT1_pow_relations n m 0 s hn hm hmn (Nat.zero_le _) hs).2.2.2.1 h
lemma ii2 (hs : s ≤ n) (h : s + m = n + 1) : (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ m :=
  (CT1_pow_relations n m 0 s hn hm hmn (Nat.zero_le _) hs).2.2.2.2.1 h
lemma ii3 (hs : s ≤ n) (h : s + m ≤ n) :
    (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ m * (XT1 (s + m))⁻¹ :=
  (CT1_pow_relations n m 0 s hn hm hmn (Nat.zero_le _) hs).2.2.2.2.2.1 h
lemma iii : CT1 n ^ m = XT1 (n + 1 - m) * CT1 (n + 1) ^ m :=
  (CT1_pow_relations n m 0 0 hn hm hmn (Nat.zero_le _) (Nat.zero_le _)).2.2.2.2.2.2.1
lemma iv : CT1 n ^ m = CT1 (n + 1) ^ (m + 1) * (XT1 (m - 1))⁻¹ :=
  (CT1_pow_relations n m 0 0 hn hm hmn (Nat.zero_le _) (Nat.zero_le _)).2.2.2.2.2.2.2.1
end

lemma v (n : ℕ) (hn : 0 < n) : CT1 n ^ (n + 2) = 1 :=
  (CT1_pow_relations n 1 0 0 hn le_rfl (by omega) (Nat.zero_le _) (Nat.zero_le _)).2.2.2.2.2.2.2.2

/-! ### Pushing words through powers of `Cₙ` -/

lemma pushLeft : ∀ (l : List ℕ) (n m : ℕ), 0 < n → 1 ≤ m → m ≤ n + 1 → (∀ r ∈ l, r ≤ n) →
    ∃ l' n' m', 0 < n' ∧ 1 ≤ m' ∧ m' ≤ n' + 1 ∧ CT1 n ^ m * P l = P l' * CT1 n' ^ m' := by
  intro l
  induction l with
  | nil => intro n m hn hm hmn _; exact ⟨[], n, m, hn, hm, hmn, by simp⟩
  | cons r l ih =>
    intro n m hn hm hmn hl
    have hr : r ≤ n := hl r (by simp)
    have hl' : ∀ x ∈ l, x ≤ n + 1 := fun x hx => (hl x (by simp [hx])).trans (Nat.le_succ n)
    rcases (show m ≤ r ∨ r + 1 = m ∨ r + 1 < m by omega) with h | h | h
    · obtain ⟨l', n', m', h1, h2, h3, e⟩ := ih (n + 1) m (by omega) hm (by omega) hl'
      refine ⟨(r - m) :: l', n', m', h1, h2, h3, ?_⟩
      rw [P_cons, ← mul_assoc, i1 hn hm hmn hr h, mul_assoc, e, P_cons, mul_assoc]
    · obtain ⟨l', n', m', h1, h2, h3, e⟩ := ih (n + 1) (m + 1) (by omega) (by omega) (by omega) hl'
      exact ⟨l', n', m', h1, h2, h3, by rw [P_cons, ← mul_assoc, i2 hn hm hmn hr h, e]⟩
    · obtain ⟨l', n', m', h1, h2, h3, e⟩ := ih (n + 1) (m + 1) (by omega) (by omega) (by omega) hl'
      refine ⟨(r + (n + 2 - m)) :: l', n', m', h1, h2, h3, ?_⟩
      rw [P_cons, ← mul_assoc, i3 hn hm hmn hr h, mul_assoc, e, P_cons, mul_assoc]

lemma pushRight : ∀ (l : List ℕ) (n m : ℕ), 0 < n → 1 ≤ m → m ≤ n + 1 → (∀ s ∈ l, s ≤ n) →
    ∃ l' n' m', 0 < n' ∧ 1 ≤ m' ∧ m' ≤ n' + 1 ∧ (P l)⁻¹ * CT1 n ^ m = CT1 n' ^ m' * (P l')⁻¹ := by
  intro l
  induction l with
  | nil => intro n m hn hm hmn _; exact ⟨[], n, m, hn, hm, hmn, by simp⟩
  | cons s l ih =>
    intro n m hn hm hmn hl
    have hs : s ≤ n := hl s (by simp)
    have hl' : ∀ x ∈ l, x ≤ n + 1 := fun x hx => (hl x (by simp [hx])).trans (Nat.le_succ n)
    have hinv : (P (s :: l))⁻¹ = (P l)⁻¹ * (XT1 s)⁻¹ := by rw [P_cons, mul_inv_rev]
    rcases (show n + 2 ≤ s + m ∨ s + m = n + 1 ∨ s + m ≤ n by omega) with h | h | h
    · obtain ⟨l', n', m', h1, h2, h3, e⟩ := ih (n + 1) (m + 1) (by omega) (by omega) (by omega) hl'
      refine ⟨(s + m - (n + 2)) :: l', n', m', h1, h2, h3, ?_⟩
      rw [hinv, mul_assoc, ii1 hn hm hmn hs h, ← mul_assoc, e, P_cons, mul_inv_rev, mul_assoc]
    · obtain ⟨l', n', m', h1, h2, h3, e⟩ := ih (n + 1) m (by omega) hm (by omega) hl'
      exact ⟨l', n', m', h1, h2, h3, by rw [hinv, mul_assoc, ii2 hn hm hmn hs h, e]⟩
    · obtain ⟨l', n', m', h1, h2, h3, e⟩ := ih (n + 1) m (by omega) hm (by omega) hl'
      refine ⟨(s + m) :: l', n', m', h1, h2, h3, ?_⟩
      rw [hinv, mul_assoc, ii3 hn hm hmn hs h, ← mul_assoc, e, P_cons, mul_inv_rev, mul_assoc]

lemma raiseUp : ∀ (k n m : ℕ), 0 < n → 1 ≤ m → m ≤ n + 1 →
    ∃ l, CT1 n ^ m = P l * CT1 (n + k) ^ m := by
  intro k
  induction k with
  | zero => intro n m _ _ _; exact ⟨[], by simp⟩
  | succ k ih =>
    intro n m hn hm hmn
    obtain ⟨l, e⟩ := ih n m hn hm hmn
    refine ⟨l ++ [n + k + 1 - m], ?_⟩
    rw [e, iii (n := n + k) (by omega) hm (by omega), P_append, ← mul_assoc]
    simp [P, mul_assoc, show n + k + 1 = n + (k + 1) by omega]

lemma raiseDown : ∀ (k n m : ℕ), 0 < n → 1 ≤ m → m ≤ n + 1 →
    ∃ l, CT1 n ^ m = CT1 (n + k) ^ (m + k) * (P l)⁻¹ := by
  intro k
  induction k with
  | zero => intro n m _ _ _; exact ⟨[], by simp⟩
  | succ k ih =>
    intro n m hn hm hmn
    obtain ⟨l, e⟩ := ih n m hn hm hmn
    refine ⟨l ++ [m + k - 1], ?_⟩
    rw [e, iv (n := n + k) (m := m + k) (by omega) (by omega) (by omega),
      show n + k + 1 = n + (k + 1) by omega, show m + k + 1 = m + (k + 1) by omega]
    simp [P_append, P, mul_assoc]

lemma reduceExp (N e : ℕ) (hN : 0 < N) : CT1 N ^ e = CT1 N ^ (e % (N + 2)) := by
  conv_lhs => rw [← Nat.div_add_mod e (N + 2), pow_add, pow_mul, v N hN, one_pow, one_mul]

lemma combine (n m n₂ m₂ : ℕ) (hn : 0 < n) (hm : 1 ≤ m) (hmn : m ≤ n + 1)
    (hn₂ : 0 < n₂) (hm₂ : 1 ≤ m₂) (hmn₂ : m₂ ≤ n₂ + 1) :
    ∃ l₁ l₂ N M, M < N + 2 ∧ CT1 n ^ m * CT1 n₂ ^ m₂ = P l₁ * CT1 N ^ M * (P l₂)⁻¹ := by
  set N := max n n₂
  obtain ⟨l₁, e₁⟩ := raiseUp (N - n) n m hn hm hmn
  obtain ⟨l₂, e₂⟩ := raiseDown (N - n₂) n₂ m₂ hn₂ hm₂ hmn₂
  rw [show n + (N - n) = N by omega] at e₁
  rw [show n₂ + (N - n₂) = N by omega] at e₂
  refine ⟨l₁, l₂, N, (m + (m₂ + (N - n₂))) % (N + 2), Nat.mod_lt _ (by omega), ?_⟩
  rw [e₁, e₂, ← reduceExp N _ (by omega), pow_add]
  group

/-! ### The normal form of `F`, carried into `T₁` -/

/-- `Yᵢ^{c₀} Yᵢ₊₁^{c₁} ⋯` in `F₁`. -/
def wordY (i : ℕ) : List ℕ → F1
  | [] => 1
  | c :: cs => Y i ^ c * wordY (i + 1) cs

def expand (i : ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs => List.replicate c i ++ expand (i + 1) cs

lemma fromF1_wordY (i : ℕ) (cs : List ℕ) : fromF1 (wordY i cs) = P (expand i cs) := by
  induction cs generalizing i with
  | nil => simp [wordY, expand]
  | cons c cs ih => simp [wordY, expand, map_mul, map_pow, fromF1_Y, ih, P_append, P_replicate]

lemma nf (l : List ℕ) (i : ℕ) : ∃ l₁ l₂, (P l)⁻¹ * XT1 i = P l₁ * (P l₂)⁻¹ := by
  obtain ⟨e34, he34A, he34B⟩ := exists_mulEquiv_F1_F
  let Φ : F1 →* (UI ≃o UI) := F.subtype.comp e34.toMonoidHom
  have hΦinj : Function.Injective Φ := Subtype.val_injective.comp e34.injective
  have hΦY : ∀ j, Φ (Y j) = X j := by
    intro j; cases j <;> simp [Φ, Y, X, map_mul, map_inv, map_pow, he34A, he34B]
  have hΦw : ∀ j cs, Φ (wordY j cs) = wordFrom j cs := by
    intro j cs
    induction cs generalizing j with
    | nil => simp [wordY, wordFrom]
    | cons c cs ih => simp [wordY, wordFrom, map_mul, map_pow, hΦY, ih]
  let PY : F1 := (l.map Y).prod
  have hPY : fromF1 PY = P l := by simp [PY, P, map_list_prod, List.map_map, Function.comp_def, fromF1_Y]
  let z : F1 := PY⁻¹ * Y i
  have hz : fromF1 z = (P l)⁻¹ * XT1 i := by simp [z, map_mul, map_inv, hPY, fromF1_Y]
  rw [← hz]
  by_cases h1 : e34 z = 1
  · have : z = 1 := e34.injective (h1.trans (map_one e34).symm)
    exact ⟨[], [], by simp [this]⟩
  · have hne : ((e34 z : F) : UI ≃o UI) ≠ 1 := fun h => h1 (Subtype.ext h)
    obtain ⟨⟨q₁, q₂⟩, ⟨-, hf⟩, -⟩ := existsUnique_normalForm (e34 z).2 hne
    have : z = wordY 0 q₂ * (wordY 0 q₁)⁻¹ := by
      apply hΦinj
      rw [show Φ z = ((e34 z : F) : UI ≃o UI) from rfl, hf, map_mul, map_inv, hΦw, hΦw]
      rfl
    exact ⟨expand 0 q₂, expand 0 q₁, by rw [this, map_mul, map_inv, fromF1_wordY, fromF1_wordY]⟩

/-! ### The set `H` -/

def InH (g : T1) : Prop := ∃ l₁ l₂ n m, m < n + 2 ∧ g = P l₁ * CT1 n ^ m * (P l₂)⁻¹

lemma letters_le (l : List ℕ) : ∀ r ∈ l, r ≤ l.sum := fun r hr => List.le_sum_of_mem hr

lemma CT1_pow_eq_one_of (n m : ℕ) (h : n = 0 ∨ m = 0) : CT1 n ^ m = 1 := by
  rcases h with rfl | rfl <;> simp [CT1]

lemma InH_mul_X {g : T1} (hg : InH g) (i : ℕ) : InH (g * XT1 i) := by
  obtain ⟨l₁, l₂, n, m, hmn, rfl⟩ := hg
  obtain ⟨l₃, l₄, e⟩ := nf l₂ i
  have hg : P l₁ * CT1 n ^ m * (P l₂)⁻¹ * XT1 i = P l₁ * (CT1 n ^ m * P l₃) * (P l₄)⁻¹ := by
    rw [mul_assoc (P l₁ * _), e]; group
  rw [hg]
  by_cases h0 : n = 0 ∨ m = 0
  · exact ⟨l₁ ++ l₃, l₄, 0, 0, by omega, by rw [CT1_pow_eq_one_of n m h0, P_append]; simp⟩
  · push Not at h0
    obtain ⟨l₅, e₅⟩ := raiseUp l₃.sum n m (by omega) (by omega) (by omega)
    obtain ⟨l₆, n', m', h1, h2, h3, e₆⟩ :=
      pushLeft l₃ (n + l₃.sum) m (by omega) (by omega) (by omega)
        (fun r hr => (letters_le l₃ r hr).trans (by omega))
    refine ⟨l₁ ++ l₅ ++ l₆, l₄, n', m', by omega, ?_⟩
    rw [e₅, mul_assoc (P l₅), e₆, P_append, P_append]; group

lemma InH_mul_X_inv {g : T1} (hg : InH g) (i : ℕ) : InH (g * (XT1 i)⁻¹) := by
  obtain ⟨l₁, l₂, n, m, hmn, rfl⟩ := hg
  exact ⟨l₁, i :: l₂, n, m, hmn, by rw [P_cons, mul_inv_rev]; group⟩

lemma InH_mul_C {g : T1} (hg : InH g) : InH (g * genC) := by
  obtain ⟨l₁, l₂, n, m, hmn, rfl⟩ := hg
  obtain ⟨l₅, e₅⟩ := raiseDown l₂.sum 1 1 (by omega) le_rfl (by omega)
  obtain ⟨l₆, n', m', h1, h2, h3, e₆⟩ :=
    pushRight l₂ (1 + l₂.sum) (1 + l₂.sum) (by omega) (by omega) (by omega)
      (fun r hr => (letters_le l₂ r hr).trans (by omega))
  have hc : genC = CT1 1 ^ 1 := by rw [pow_one, CT1_one]
  have key : (P l₂)⁻¹ * genC = CT1 n' ^ m' * (P (l₅ ++ l₆))⁻¹ := by
    rw [hc, e₅, ← mul_assoc, e₆, P_append, mul_inv_rev, mul_assoc]
  have hg : P l₁ * CT1 n ^ m * (P l₂)⁻¹ * genC = P l₁ * (CT1 n ^ m * CT1 n' ^ m') * (P (l₅ ++ l₆))⁻¹ := by
    rw [mul_assoc (P l₁ * _), key]; group
  rw [hg]
  by_cases h0 : n = 0 ∨ m = 0
  · exact ⟨l₁, l₅ ++ l₆, n', m', by omega, by rw [CT1_pow_eq_one_of n m h0, one_mul]⟩
  · push Not at h0
    obtain ⟨l₇, l₈, N, M, hM, e₇⟩ := combine n m n' m' (by omega) (by omega) (by omega) h1 h2 h3
    refine ⟨l₁ ++ l₇, l₅ ++ l₆ ++ l₈, N, M, hM, ?_⟩
    rw [e₇]; simp only [P_append]; group

theorem exists_eq_mul_CT1_pow_mul_inv' (g : T1) :
    ∃ (p q : T1) (m n : ℕ), IsPositiveT1 p ∧ IsPositiveT1 q ∧ m < n + 2 ∧
      g = p * CT1 n ^ m * q⁻¹ := by
  have hall : ∀ g : T1, InH g := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range (PresentedGroup.of : FormalABC → T1)) := by
      rw [PresentedGroup.closure_range_of]; trivial
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨[], [], 0, 0, by omega, by simp⟩
    | mul_right x _ y hy ih =>
      obtain ⟨s, rfl⟩ := hy
      cases s
      · exact InH_mul_X ih 0
      · simpa [XT1_one] using InH_mul_X ih 1
      · exact InH_mul_C ih
    | mul_inv_cancel x _ y hy ih =>
      obtain ⟨s, rfl⟩ := hy
      cases s
      · exact InH_mul_X_inv ih 0
      · simpa [XT1_one] using InH_mul_X_inv ih 1
      · have : genC⁻¹ = genC * genC := by
          have := rel6
          calc genC⁻¹ = genC⁻¹ * genC ^ 3 := by rw [this, mul_one]
            _ = genC * genC := by group; exact sq genC
        rw [this, ← mul_assoc]
        exact InH_mul_C (InH_mul_C ih)
  obtain ⟨l₁, l₂, n, m, hmn, e⟩ := hall g
  exact ⟨P l₁, P l₂, m, n, isPositive_P l₁, isPositive_P l₂, hmn, e⟩

end CannonFloydParry.S5

open CannonFloydParry

theorem solution (g : T1) :
    ∃ (p q : T1) (m n : ℕ), IsPositiveT1 p ∧ IsPositiveT1 q ∧ m < n + 2 ∧
      g = p * CT1 n ^ m * q⁻¹ :=
  CannonFloydParry.S5.exists_eq_mul_CT1_pow_mul_inv' g
