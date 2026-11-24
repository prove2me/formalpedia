-- Prove2me | solution 1 for DepthOneQExp.U_mem_depthOneSet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:23:56.8018+00:00
-- url     : https://prove2.me/submissions/a0303a8b-6ce8-4e14-85e6-0d1e1b24ad88

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_DepthOneQExp_xGate
import Definitions.Def_DepthOneQExp_zGate
import Definitions.Def_DepthOneQExp_cnotGate
import Definitions.Def_DepthOneQExp_U

open DepthOneQExp MITMSynthesis

namespace DepthOneQExp.DepthAux

theorem cnotPerm_mod (n a b : ℕ) : cnotPerm n (a % n) (b % n) = cnotPerm n a b := by
  ext x k
  simp [cnotPerm, bit]

theorem cnotPerm_apply' (n a b : ℕ) (x : Q n) : cnotPerm n a b x =
    fun k : Fin n => if (k : ℕ) = b % n ∧ a % n ≠ b % n then x k + bit x a else x k := rfl

def pairFn (n : ℕ) (hn : 0 < n) (c t : ℕ) : Fin 2 → Fin n :=
  fun i => if (i : ℕ) = 0 then ⟨c % n, Nat.mod_lt _ hn⟩ else ⟨t % n, Nat.mod_lt _ hn⟩

theorem pairFn_inj (n : ℕ) (hn : 0 < n) (c t : ℕ) (h : c % n ≠ t % n) :
    Function.Injective (pairFn n hn c t) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [pairFn, Fin.ext_iff]

/-- CNOT placed with control `c % n` and target `t % n`. -/
noncomputable def cnotPlace (n : ℕ) (hn : 0 < n) (c t : ℕ) (h : c % n ≠ t % n) : Placement n :=
  ⟨cnotGate, ⟨pairFn n hn c t, pairFn_inj n hn c t h⟩⟩

theorem cnotPlace_unitary (n : ℕ) (hn : 0 < n) (c t : ℕ) (h : c % n ≠ t % n) :
    (cnotPlace n hn c t h).unitary = permToMatrix (cnotPerm n c t) := by
  ext x y
  show (if (∀ j, j ∉ Set.range (pairFn n hn c t) → x j = y j) then
      (if x ∘ pairFn n hn c t = cnotPerm 2 0 1 (y ∘ pairFn n hn c t) then (1 : ℂ) else 0) else 0) =
    if x = cnotPerm n c t y then 1 else 0
  have key : (x = cnotPerm n c t y) ↔ ((∀ j, j ∉ Set.range (pairFn n hn c t) → x j = y j) ∧
      (x ∘ pairFn n hn c t) = cnotPerm 2 0 1 (y ∘ pairFn n hn c t)) := by
    have hc := Nat.mod_lt c hn
    have ht := Nat.mod_lt t hn
    have hb : bit y c = y ⟨c % n, hc⟩ := by simp [bit, hc]
    have hb2 : ∀ v : Q 2, bit v 0 = v 0 := fun v => by simp [bit]
    simp only [cnotPerm_apply', hb, hb2]
    constructor
    · rintro rfl
      refine ⟨fun j hj => ?_, ?_⟩
      · have : (j : ℕ) ≠ t % n := fun e => hj ⟨1, by simp [pairFn, Fin.ext_iff, e]⟩
        simp [this]
      · funext i
        fin_cases i
        · simp [pairFn, h]
        · simp [pairFn, h]
    · rintro ⟨h1, h2⟩
      funext k
      have e0 := congrFun h2 0
      have e1 := congrFun h2 1
      simp [pairFn] at e0 e1
      by_cases hk : (k : ℕ) = t % n
      · have : k = ⟨t % n, ht⟩ := Fin.ext hk
        subst this
        simpa [h] using e1
      · by_cases hk' : (k : ℕ) = c % n
        · have : k = ⟨c % n, hc⟩ := Fin.ext hk'
          subst this
          simpa [hk] using e0
        · rw [if_neg (fun e => hk e.1)]
          apply h1
          rintro ⟨i, hi⟩
          fin_cases i <;> simp [pairFn, Fin.ext_iff] at hi <;> omega
  by_cases h1 : x = cnotPerm n c t y
  · have := key.1 h1
    rw [if_pos this.1, if_pos this.2, if_pos h1]
  · rw [if_neg h1]
    split_ifs with h2 h3
    · exact absurd (key.2 ⟨h2, h3⟩) h1
    · rfl
    · rfl

theorem mod3_eq (s i a : ℕ) : (3 * i + a) % (3 * s) % 3 = a % 3 := by
  rw [Nat.mod_mod_of_dvd _ (Dvd.intro s rfl)]
  omega

theorem mod_inj (s i j a : ℕ) (hi : i < s) (hj : j < s)
    (h : (3 * i + a) % (3 * s) = (3 * j + a) % (3 * s)) : i = j := by
  have h1 : 3 * i + a ≡ 3 * j + a [MOD 3 * s] := h
  have h2 : 3 * i ≡ 3 * j [MOD 3 * s] := Nat.ModEq.add_right_cancel' a h1
  have h3 : i ≡ j [MOD s] := Nat.ModEq.mul_left_cancel' (by norm_num) h2
  have := h3
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

theorem ne_of_mod3 (s i j a b : ℕ) (hab : a % 3 ≠ b % 3) :
    (3 * i + a) % (3 * s) ≠ (3 * j + b) % (3 * s) := by
  intro h
  have := congrArg (· % 3) h
  simp only [mod3_eq] at this
  exact hab this

theorem single_cnot_mem (n a b : ℕ) (hn : 0 < n) (h : a % n ≠ b % n) :
    permToMatrix (cnotPerm n a b) ∈ depthOneSet n {xGate, zGate, cnotGate} := by
  refine ⟨[cnotPlace n hn a b h], ⟨by simp, by simp [cnotPlace], by simp⟩, ?_⟩
  simp [layerUnitary, cnotPlace_unitary]

theorem layer_cnot_mem (s a b : ℕ) (hs : 1 ≤ s) (hab : a % 3 ≠ b % 3) :
    ((List.range s).map fun i => permToMatrix (cnotPerm (3 * s) (3 * i + a) (3 * i + b))).prod ∈
      depthOneSet (3 * s) {xGate, zGate, cnotGate} := by
  have hn : 0 < 3 * s := by omega
  refine ⟨(List.range s).map fun i => cnotPlace (3 * s) hn (3 * i + a) (3 * i + b)
      (ne_of_mod3 s i i a b hab), ⟨?_, ?_, ?_⟩, ?_⟩
  · simp; omega
  · simp [cnotPlace]
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range (n := s))
    intro i j hi hj hij
    rw [List.mem_range] at hi hj
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨l, hl⟩
    simp only [cnotPlace, Function.Embedding.coeFn_mk] at hl
    fin_cases k <;> fin_cases l <;> simp [pairFn, Fin.ext_iff] at hl
    · exact absurd (mod_inj s j i a hj hi hl) (by omega)
    · exact ne_of_mod3 s j i b a (Ne.symm hab) hl
    · exact ne_of_mod3 s j i a b hab hl
    · exact absurd (mod_inj s j i b hj hi hl) (by omega)
  · simp only [layerUnitary, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp [cnotPlace_unitary]

theorem xPerm_apply' (n j : ℕ) (x : Q n) : xPerm n j x =
    fun k : Fin n => if (k : ℕ) = j % n then x k + 1 else x k := rfl

noncomputable def onePlace (n : ℕ) (hn : 0 < n) (g : Gate) (hg : g.arity = 1) : Placement n :=
  ⟨g, ⟨fun _ => ⟨0, hn⟩, by
    intro i j _
    have : Subsingleton (Fin g.arity) := by rw [hg]; infer_instance
    exact Subsingleton.elim i j⟩⟩

theorem x_mem (n : ℕ) (hn : 0 < n) :
    permToMatrix (xPerm n 0) ∈ depthOneSet n {xGate, zGate, cnotGate} := by
  refine ⟨[onePlace n hn xGate rfl], ⟨by simp, by simp [onePlace], by simp⟩, ?_⟩
  simp only [layerUnitary, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ext x y
  show (if (∀ j, j ∉ Set.range (fun _ : Fin 1 => (⟨0, hn⟩ : Fin n)) → x j = y j) then
      (if (fun _ : Fin 1 => x ⟨0, hn⟩) = xPerm 1 0 (fun _ : Fin 1 => y ⟨0, hn⟩) then (1 : ℂ) else 0) else 0) =
    if x = xPerm n 0 y then 1 else 0
  have key : x = xPerm n 0 y ↔ ((∀ j, j ∉ Set.range (fun _ : Fin 1 => (⟨0, hn⟩ : Fin n)) → x j = y j) ∧
      (fun _ : Fin 1 => x ⟨0, hn⟩) = xPerm 1 0 (fun _ : Fin 1 => y ⟨0, hn⟩)) := by
    simp only [xPerm_apply', Nat.zero_mod]
    constructor
    · rintro rfl
      refine ⟨fun j hj => ?_, ?_⟩
      · have : (j : ℕ) ≠ 0 := fun e => hj ⟨0, by ext; simp [e]⟩
        simp [this]
      · funext i
        simp
    · rintro ⟨h1, h2⟩
      funext k
      have e0 := congrFun h2 0
      simp at e0
      by_cases hk : (k : ℕ) = 0
      · have : k = ⟨0, hn⟩ := Fin.ext hk
        subst this
        simpa using e0
      · simp only [hk, if_false]
        apply h1
        rintro ⟨i, hi⟩
        exact hk (by rw [← hi])
  by_cases h1 : x = xPerm n 0 y
  · have := key.1 h1
    rw [if_pos this.1, if_pos this.2, if_pos h1]
  · rw [if_neg h1]
    split_ifs with h2 h3
    · exact absurd (key.2 ⟨h2, h3⟩) h1
    · rfl
    · rfl

theorem z_mem (n : ℕ) (hn : 0 < n) :
    zMat n 0 ∈ depthOneSet n {xGate, zGate, cnotGate} := by
  refine ⟨[onePlace n hn zGate rfl], ⟨by simp, by simp [onePlace], by simp⟩, ?_⟩
  simp only [layerUnitary, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ext x y
  show (if (∀ j, j ∉ Set.range (fun _ : Fin 1 => (⟨0, hn⟩ : Fin n)) → x j = y j) then
      zMat 1 0 (fun _ : Fin 1 => x ⟨0, hn⟩) (fun _ : Fin 1 => y ⟨0, hn⟩) else 0) = zMat n 0 x y
  have hbx : bit x 0 = x ⟨0, hn⟩ := by simp [bit, hn]
  simp only [zMat, Matrix.diagonal_apply, hbx]
  have hb1 : ∀ v : Q 1, bit v 0 = v 0 := fun v => by simp [bit]
  simp only [hb1]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [if_neg hxy]
    by_cases h1 : ∀ j, j ∉ Set.range (fun _ : Fin 1 => (⟨0, hn⟩ : Fin n)) → x j = y j
    · rw [if_pos h1]
      have h2 : ¬ (fun _ : Fin 1 => x ⟨0, hn⟩) = (fun _ : Fin 1 => y ⟨0, hn⟩) := by
        intro h2
        apply hxy
        funext k
        by_cases hk : (k : ℕ) = 0
        · have : k = ⟨0, hn⟩ := Fin.ext hk
          subst this
          exact congrFun h2 0
        · apply h1
          rintro ⟨i, hi⟩
          exact hk (by rw [← hi])
      rw [if_neg h2]
    · rw [if_neg h1]

end DepthOneQExp.DepthAux

open DepthOneQExp.DepthAux in
theorem solution (s : ℕ) (hs : 1 ≤ s) (i : Fin 16) :
    U s i ∈ MITMSynthesis.depthOneSet (3 * s) {xGate, zGate, cnotGate} := by
  have hn : 0 < 3 * s := by omega
  have hsingle : ∀ a b : ℕ, a < 3 → b < 3 → a ≠ b →
      permToMatrix (cnotPerm (3 * s) a b) ∈ depthOneSet (3 * s) {xGate, zGate, cnotGate} := by
    intro a b ha hb hab
    apply single_cnot_mem _ _ _ hn
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact hab
  unfold U
  dsimp only
  fin_cases i <;> simp only [Fin.reduceFinMk, Matrix.cons_val]
  · exact x_mem _ hn
  · exact z_mem _ hn
  all_goals first
    | exact hsingle _ _ (by norm_num) (by norm_num) (by norm_num)
    | exact layer_cnot_mem s _ _ hs (by norm_num)
