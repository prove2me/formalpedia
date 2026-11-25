-- Prove2me | solution 1 for DetDLP.m13a_irred_poly_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T01:40:21.073842+00:00
-- url     : https://prove2.me/submissions/da87fad5-43e4-4bd8-8c84-3e42e8e4f2f3

import Definitions.Def_DetDLP_M13A_IrredHermite
import Definitions.Def_ToTuring_Lib_List2

open DetDLP_M13A_IrredHermite Polynomial
set_option autoImplicit false
namespace DetDLP_M13A_IrredProof

private abbrev F := ZMod 2
private noncomputable abbrev pol := polynomial F

private theorem deg_lt (R : Type*) [Semiring R] [Nontrivial R] (w : List Bool) :
    (polynomial R w).degree < (w.length : ℕ) := by
  induction w with
  | nil => simp [polynomial]
  | cons b w ih =>
    rw [polynomial, List.length_cons, Nat.cast_succ]
    apply lt_of_le_of_lt (degree_add_le ..)
    apply max_lt
    · cases b <;> simp
      exact_mod_cast Nat.lt_succ_self w.length
    · exact lt_trans ih (by exact_mod_cast Nat.lt_succ_self w.length)

private theorem monic_word (R : Type*) [Semiring R] [Nontrivial R] (w : List Bool) :
    (polynomial R (true :: w)).Monic ∧ (polynomial R (true :: w)).natDegree = w.length := by
  simp only [polynomial, Bool.toNat_true, Nat.cast_one, map_one, one_mul]
  have h := deg_lt R w
  refine ⟨monic_X_pow_add h, natDegree_eq_of_degree_eq_some ?_⟩
  rw [degree_add_eq_left_of_degree_lt, degree_X_pow]; simpa using h

private theorem xor_len (g r : List Bool) (h : g.length ≤ r.length) :
    (((g.zip r).map (fun p => p.1 ^^ p.2)) ++ r.drop g.length).length = r.length := by
  simp [List.length_zip, min_eq_left h]; omega

private theorem xor_pol (g r : List Bool) (h : g.length ≤ r.length) :
    pol (((g.zip r).map (fun p => p.1 ^^ p.2)) ++ r.drop g.length) =
    pol r + pol g * X ^ (r.length - g.length) := by
  induction g generalizing r with
  | nil => simp [polynomial]
  | cons a g ih =>
    cases r with
    | nil => simp at h
    | cons b r =>
      have e : g.length ≤ r.length := by simpa using h
      simp only [List.zip_cons_cons, List.map_cons, List.cons_append, List.length_cons,
        List.drop_succ_cons, polynomial, xor_len g r e, ih r e, Nat.add_sub_add_right]
      have hc : (C (((a ^^ b).toNat : ℕ) : F) : F[X]) = C (b.toNat : F) + C (a.toNat : F) := by
        rw [← map_add]; congr 1; cases a <;> cases b <;> decide
      have ep : (X : F[X])^g.length * X^(r.length-g.length) = X^r.length := by
        rw [← pow_add]; congr 1; omega
      rw [hc, add_mul, add_mul, mul_assoc, ep]; ring

private theorem step_len (g r : List Bool) : (divStep g r).length =
    if g.length < r.length then r.length - 1 else r.length := by
  unfold divStep; split_ifs with h h2 <;> simp_all [xor_len, List.length_tail,
    show ∀ (h : g.length < r.length), g.length ≤ r.length - 1 by omega] <;> omega

private theorem step_dvd (g r : List Bool) :
    pol (true :: g) ∣ pol (divStep g r) ↔ pol (true :: g) ∣ pol r := by
  unfold divStep; split_ifs with h h2
  · cases r with
    | nil => simp at h
    | cons b r =>
      simp at h2; subst b
      have e : g.length ≤ r.length := by simp only [List.length_cons] at h; omega
      simp only [List.tail_cons, xor_pol g r e]
      have E : pol r + pol g * X ^ (r.length-g.length) = pol (true :: r) +
          pol (true :: g) * X^(r.length-g.length) := by
        simp only [polynomial, Bool.toNat_true, Nat.cast_one, map_one, one_mul, add_mul,
          ← pow_add, Nat.add_sub_of_le e]
        have H : (2 : F[X]) = 0 := by exact CharP.cast_eq_zero _ 2
        linear_combination -(X^(r.length) : F[X]) * H
      rw [E]; exact dvd_add_left (dvd_mul_right ..)
  · cases r with
    | nil => rfl
    | cons b r => simp at h2; subst b; simp [polynomial]
  · rfl

private theorem rem_spec (g f : List Bool) :
    (remainder g f).length ≤ g.length ∧
    (pol (true :: g) ∣ pol (remainder g f) ↔ pol (true :: g) ∣ pol f) := by
  suffices H : ∀ l r : List Bool, r.length ≤ g.length + l.length →
      (l.foldl (fun r _ => divStep g r) r).length ≤ g.length ∧
      (pol (true :: g) ∣ pol (l.foldl (fun r _ => divStep g r) r) ↔ pol (true :: g) ∣ pol r) from H f f (by omega)
  intro l; induction l with
  | nil => simp
  | cons b l ih =>
    intro r h; simp only [List.foldl_cons]
    have e : (divStep g r).length ≤ g.length + l.length := by
      rw [step_len]; simp only [List.length_cons] at h; split <;> omega
    exact ⟨(ih _ e).1, (ih _ e).2.trans (step_dvd ..)⟩

private theorem any_pol (r : List Bool) : r.any id = true ↔ pol r ≠ 0 := by
  induction r with
  | nil => simp [polynomial]
  | cons b r ih => cases b with
    | false => simpa [polynomial] using ih
    | true => simp [(monic_word F r).1.ne_zero]

private theorem remainder_test (g f : List Bool) : (remainder g f).any id = true ↔
    ¬pol (true :: g) ∣ pol f := by
  obtain ⟨hl, hd⟩ := rem_spec g f
  rw [any_pol, ← hd]; apply not_congr; constructor
  · intro e; rw [e]; exact dvd_zero _
  · intro hd; by_contra h
    have hb := degree_le_of_dvd hd h
    have hlt := deg_lt F (remainder g f)
    rw [degree_eq_natDegree (monic_word F g).1.ne_zero, (monic_word F g).2] at hb
    exact (not_lt_of_ge (Nat.cast_le.mpr hl)) (hb.trans_lt hlt)

private theorem cap_eq (p : List ℕ) : capacity p = 2 ^ p.length := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    change Nat.bit false (capacity p) = 2^(p.length+1)
    rw [Nat.bit_val, ih, pow_succ]; simp [mul_comm]

private theorem mask_exists (g : List Bool) : ∃ z < 2 ^ g.length, word (List.range g.length) z = g := by
  induction g with
  | nil => exact ⟨0, by decide, rfl⟩
  | cons b g ih =>
    obtain ⟨z,hz,he⟩ := ih
    refine ⟨Nat.bit b z, ?_, ?_⟩
    · rw [List.length_cons, pow_succ, Nat.bit_val]; cases b <;> simp <;> omega
    · simp only [word, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        Nat.testBit_bit_zero, Function.comp_def, Nat.testBit_bit_succ]; exact congrArg (b :: ·) he

private theorem candidate_iff {n B : ℕ} (hb : 2^n ≤ B) (g : List Bool) :
    g ∈ candidates (List.range n) (List.range B) ↔ g.length = n := by
  simp only [candidates, cap_eq, List.length_range, List.take_range, min_eq_left hb,
    List.mem_map, List.mem_range]
  constructor
  · rintro ⟨z,hz,rfl⟩; simp [word]
  · intro e; subst n; exact mask_exists g

private theorem as_word (n : ℕ) (p : F[X]) (hd : p.degree < n) :
    ∃ g : List Bool, g.length = n ∧ pol g = p := by
  induction n generalizing p with
  | zero =>
    have h := (degree_lt_iff_coeff_zero _ _).mp hd
    refine ⟨[],rfl,?_⟩; ext i; simpa [polynomial] using (h i (Nat.zero_le _)).symm
  | succ n ih =>
    let q := p - C (p.coeff n) * X^n
    have hq : q.degree < n := by
      rw [degree_lt_iff_coeff_zero]; intro m hm
      simp only [q, coeff_sub, coeff_C_mul_X_pow]; split_ifs with e
      · subst m; simp
      · rw [(degree_lt_iff_coeff_zero _ _).mp hd m (by omega), sub_zero]
    obtain ⟨g,hl,he⟩ := ih q hq
    have hc : ∃ b : Bool, (b.toNat : F) = p.coeff n := by
      let c := p.coeff n; change ∃ b : Bool, (b.toNat : F) = c
      have hh := ZMod.val_lt c; have hc := ZMod.natCast_zmod_val c
      rcases (show c.val = 0 ∨ c.val = 1 by omega) with h|h
      · exact ⟨false, by simpa [h] using hc⟩
      · exact ⟨true, by simpa [h] using hc⟩
    obtain ⟨b,hb⟩ := hc
    exact ⟨b :: g, by simp [hl], by simp [polynomial, hl, he, hb, q]⟩

private theorem monic_repr {p : F[X]} (hp : p.Monic) :
    ∃ g : List Bool, g.length = p.natDegree ∧ pol (true :: g) = p := by
  obtain ⟨g, hg, he⟩ := as_word p.natDegree p.eraseLead (by
    rw [← degree_eq_natDegree hp.ne_zero]; exact p.degree_eraseLead_lt hp.ne_zero)
  refine ⟨g,hg,?_⟩
  simpa [polynomial, hg, he, hp.leadingCoeff, add_comm] using p.eraseLead_add_C_mul_X_pow

private theorem passes_iff {κ B : ℕ} (hk : 0 < κ) (hb : 2^κ ≤ B) (g : List Bool) (hl : g.length = κ) :
    passes (List.range κ) (List.range B) (true :: g) = true ↔ Irreducible (pol (true :: g)) := by
  obtain ⟨hm, hd⟩ := monic_word F g
  have h1 : polynomial F (true :: g) ≠ 1 := by intro e; rw [e, natDegree_one, hl] at hd; omega
  rw [hm.irreducible_iff_lt_natDegree_lt h1, hd, hl]
  simp only [passes, List.all_eq_true, List.mem_range, List.length_range, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not,
    List.take_range, Finset.mem_Ioc]
  constructor
  · intro h p hp hd
    obtain ⟨r,hr,er⟩ := monic_repr hp
    specialize h p.natDegree (by omega)
    have hb' : 2^p.natDegree ≤ B := le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hb
    rw [min_eq_left (by omega)] at h
    rcases h with h|h
    · omega
    · rw [← er]; exact (remainder_test _ _).mp (h r ((candidate_iff hb' _).mpr hr))
  · intro h d hd'
    by_cases D : 0 < d ∧ d + d ≤ κ
    · right; rw [min_eq_left (by omega)]
      intro r hr; have hh : 2^d ≤ B := le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hb
      have he := (candidate_iff hh _).mp hr
      apply (remainder_test _ _).mpr
      apply h _ (monic_word F r).1
      rw [(monic_word F r).2, he]; omega
    · left; omega

private theorem map_pol (g : List Bool) :
    (polynomial ℤ g).map (Int.castRingHom F) = pol g := by
  induction g with
  | nil => simp [polynomial]
  | cons b g ih => simp [polynomial, ih]

private theorem search_spec {κ B : ℕ} (hk : 0 < κ) (hb : 2^κ ≤ B) :
    let f := polynomial ℤ (search (List.range κ) (List.range B))
    f.Monic ∧ f.natDegree = κ ∧ Irreducible (f.map (Int.castRingHom F)) := by
  let K := GaloisField 2 κ
  obtain ⟨x,hx⟩ := Field.exists_primitive_element_of_finite_bot F K
  let p := minpoly F x
  have hi := IsIntegral.of_finite F x
  have hm : p.Monic := minpoly.monic hi
  have hd : p.natDegree = κ := ((Field.primitive_element_iff_minpoly_natDegree_eq F x).mp hx).trans
    (GaloisField.finrank 2 hk.ne')
  obtain ⟨g,hl,he⟩ := monic_repr hm
  let c := (candidates (List.range κ) (List.range B)).map (true :: ·)
  let test := passes (List.range κ) (List.range B)
  have H : (c.find? test).isSome = true := List.find?_isSome.mpr ⟨true :: g,
    List.mem_map.mpr ⟨g, (candidate_iff hb _).mpr (hl.trans hd),rfl⟩,
    (passes_iff hk hb g (hl.trans hd)).mpr (he ▸ minpoly.irreducible hi)⟩
  cases e : c.find? test with
  | none => simp [e] at H
  | some w =>
    have hw := List.mem_of_find?_eq_some e
    obtain ⟨r,hr,er⟩ := List.mem_map.mp hw; subst w
    have hlr := (candidate_iff hb _).mp hr
    have E : search (List.range κ) (List.range B) = true :: r := by
      change (c.find? test).getD [] = _; rw [e]; rfl
    dsimp only; rw [E, map_pol]
    exact ⟨(monic_word ℤ r).1, (monic_word ℤ r).2.trans hlr,
      (passes_iff hk hb r hlr).mp (List.find?_some e)⟩

private theorem cand_range_eq (p : List ℕ) {B C : ℕ} (b : 2^p.length ≤ B) (c : 2^p.length ≤ C) :
    candidates p (List.range B) = candidates p (List.range C) := by
  simp [candidates, cap_eq, List.take_range, min_eq_left b, min_eq_left c]

private theorem padded_eq (w : List Bool) (hb : 2^(w.filter id).length ≤ w.length) :
    irredMachine w = findIrredPoly (w.filter id).length := by
  let k := (w.filter id).length
  change search (List.range k) (List.range w.length) = search (List.range k) (List.range (2^k))
  have aux : ∀ p : List ℕ, p.length ≤ k → candidates p (List.range w.length) = candidates p (List.range (2^k)) := by
    intro p h; have h' := Nat.pow_le_pow_right (n:=2) (by decide) h
    exact cand_range_eq p (h'.trans hb) h'
  have hp : passes (List.range k) (List.range w.length) = passes (List.range k) (List.range (2^k)) := by
    funext f; unfold passes; congr 1; funext d
    rw [aux _ (by simp)]
  unfold search; rw [hp, aux _ (by simp)]

end DetDLP_M13A_IrredProof

open DetDLP_M13A_IrredHermite Groundwork Groundwork.PolyT
set_option autoImplicit false
namespace DetDLP_M13A_PolyProof
attribute [local fun_prop] PolyT.all PolyT.any PolyT.comp PolyT.const PolyT.filter PolyT.fst PolyT.length PolyT.map PolyT.prodMk PolyT.snd PolyT.testBit
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_cond__4c673073da15
variable {α : Type} [Enc α]

@[local fun_prop] private theorem capT {l : α → List ℕ} (hl : PolyT l) : PolyT fun x => capacity (l x) := by
  unfold capacity; apply PolyT.ofBits; fun_prop

@[local fun_prop] private theorem wordT {l : α → List ℕ} {z : α → ℕ} (hl : PolyT l) (hz : PolyT z) :
    PolyT fun x => word (l x) (z x) := by unfold word; fun_prop

@[local fun_prop] private theorem candT {l m : α → List ℕ} (hl : PolyT l) (hm : PolyT m) :
    PolyT fun x => candidates (l x) (m x) := by unfold candidates; fun_prop

@[local fun_prop] private theorem dsT {g r : α → List Bool} (hg : PolyT g) (hr : PolyT r) :
    PolyT fun x => divStep (g x) (r x) := by unfold divStep; fun_prop

private theorem dsLe (g r : List Bool) : (divStep g r).length ≤ r.length := by
  unfold divStep; split_ifs <;> simp_all [List.length_zip, List.length_tail] <;> omega

@[local fun_prop] private theorem remT {g f : α → List Bool} (hg : PolyT g) (hf : PolyT f) :
    PolyT fun x => remainder (g x) (f x) := by
  obtain ⟨t,ht,_,hb⟩ := PolyT.len_bound hf
  have h : ∀ g l r : List Bool, (l.foldl (fun r _ => divStep g r) r).length ≤ r.length := by
    intro g l; induction l with
    | nil => simp
    | cons b l ih => intro r; exact (ih _).trans (dsLe _ _)
  unfold remainder
  refine PolyT.foldl (g := fun x (r : List Bool) (_ : Bool) => divStep (g x) r) hf hf (by fun_prop) ⟨t,ht,?_⟩
  intro x k; apply le_trans _ (hb x); rw [len_bools, len_bools]; have := h (g x) ((f x).take k) (f x); omega

@[local fun_prop] private theorem passesT {l m : α → List ℕ} {f : α → List Bool} (hl : PolyT l) (hm : PolyT m) (hf : PolyT f) :
    PolyT fun x => passes (l x) (m x) (f x) := by unfold passes; fun_prop

@[local fun_prop] private theorem searchT {l m : α → List ℕ} (hl : PolyT l) (hm : PolyT m) :
    PolyT fun x => search (l x) (m x) := by unfold search; fun_prop

private theorem rangeLenT {l : α → List Bool} (hl : PolyT l) : PolyT fun x => List.range (l x).length := by
  apply PolyT.range; unfold Unary
  have H : PolyT fun x => (l x).map (fun _ => ()) := by fun_prop
  exact H.congr (fun x => by simp)

end DetDLP_M13A_PolyProof

open DetDLP_M13A_IrredProof DetDLP_M13A_PolyProof
attribute [local fun_prop] PolyT.filter PolyT.snd P2M_Groundwork_PolyT_id__1c5d0f44cc8f

theorem solution :
    Groundwork.PolyT irredMachine ∧
    (∀ κ : ℕ, 0 < κ → let f := polynomial ℤ (findIrredPoly κ)
      f.Monic ∧ f.natDegree = κ ∧ Irreducible (f.map (Int.castRingHom (ZMod 2)))) ∧
    ∀ w : List Bool, let κ := (w.filter id).length
      2 ^ κ ≤ w.length → irredMachine w = findIrredPoly κ := by
  refine ⟨searchT (rangeLenT (by fun_prop)) (rangeLenT (by fun_prop)), ?_, padded_eq⟩
  intro κ hk; exact search_spec hk le_rfl
