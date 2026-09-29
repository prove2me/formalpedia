-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.exists_map_smul_map_verschiebung_apply_basis_eq_of_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7d22fcb3-ca04-5d16-a891-60f006b3e813

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_map_smul_map_verschiebung_apply_basis_eq_of_baseChange

set_option autoImplicit false

noncomputable section

namespace P2mBce

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime]

def frobIter {R : Type} [CommRing R] : ℕ → WittVector p R → WittVector p R
  | 0, u => u
  | n + 1, u => frobIter n (WittVector.frobenius u)

theorem witt_map_frobenius {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (w : WittVector p R) :
    WittVector.map f (WittVector.frobenius w) = WittVector.frobenius (WittVector.map f w) :=
  WittVector.IsPoly.map (WittVector.frobenius_isPoly p) f w

theorem map_frobIter {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (w : WittVector p R) :
    WittVector.map f (frobIter n w) = frobIter n (WittVector.map f w) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simp only [frobIter, ih, witt_map_frobenius]

theorem frobIter_mul {R : Type} [CommRing R] (n : ℕ) (u v : WittVector p R) :
    frobIter n (u * v) = frobIter n u * frobIter n v := by
  induction n generalizing u v with
  | zero => rfl
  | succ n ih => simp only [frobIter, map_mul, ih]

theorem witt_split {R : Type} [CommRing R] (u : WittVector p R) :
    ∃ (t : R) (u' : WittVector p R), u = WittVector.teichmuller p t + WittVector.verschiebung u' := by
  set w : WittVector p R := u - WittVector.teichmuller p (u.coeff 0) with hw
  have hw0 : w.coeff 0 = 0 := by
    have : WittVector.constantCoeff w = 0 := by
      simp only [hw, map_sub, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self]
    simpa [WittVector.constantCoeff_apply] using this
  refine ⟨u.coeff 0, w.shift 1, ?_⟩
  have key := WittVector.eq_iterate_verschiebung (x := w) (n := 1) (by
    intro i hi
    have : i = 0 := by omega
    subst this; exact hw0)
  rw [Function.iterate_one] at key
  rw [← key, hw]; abel

section series

variable {R : Type} [CommRing R] {jR : Zp2 p →+* R} (E : GradedCartierModuleData p R jR)

def IsSum (x : ℕ → E.M) (s : E.M) : Prop :=
  ∀ N : ℕ, ∃ t : E.M, s = (∑ m ∈ Finset.range N, (⇑E.verschiebung)^[m] (x m)) + (⇑E.verschiebung)^[N] t

theorem iter_add (n : ℕ) (a b : E.M) :
    (⇑E.verschiebung)^[n] (a + b) = (⇑E.verschiebung)^[n] a + (⇑E.verschiebung)^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

theorem V_iterV (m : ℕ) (y : E.M) :
    E.verschiebung ((⇑E.verschiebung)^[m] y) = (⇑E.verschiebung)^[m + 1] y :=
  (Function.iterate_succ_apply' _ _ _).symm

theorem smul_iterV (u : WittVector p R) (n : ℕ) (z : E.M) :
    u • (⇑E.verschiebung)^[n] z = (⇑E.verschiebung)^[n] (frobIter n u • z) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', E.smul_verschiebung, ih, V_iterV]
    rfl

theorem peel (r : ℕ → E.M) (N : ℕ) (t : E.M) :
    r 0 + E.verschiebung ((∑ m ∈ Finset.range N, (⇑E.verschiebung)^[m] (r (m + 1))) +
        (⇑E.verschiebung)^[N] t) =
      (∑ m ∈ Finset.range (N + 1), (⇑E.verschiebung)^[m] (r m)) + (⇑E.verschiebung)^[N + 1] t := by
  rw [map_add, map_sum, Finset.sum_range_succ']
  simp only [V_iterV, Function.iterate_zero_apply]
  abel

theorem isSum_add {x y : ℕ → E.M} {s s' : E.M} (hx : IsSum E x s) (hy : IsSum E y s') :
    IsSum E (fun m => x m + y m) (s + s') := by
  intro N
  obtain ⟨t, ht⟩ := hx N
  obtain ⟨t', ht'⟩ := hy N
  refine ⟨t + t', ?_⟩
  rw [ht, ht', iter_add]
  simp only [iter_add, Finset.sum_add_distrib]
  abel

theorem isSum_smul {x : ℕ → E.M} {s : E.M} (hx : IsSum E x s) (u : WittVector p R) :
    IsSum E (fun m => frobIter m u • x m) (u • s) := by
  intro N
  obtain ⟨t, ht⟩ := hx N
  refine ⟨frobIter N u • t, ?_⟩
  rw [ht, smul_add, Finset.smul_sum, smul_iterV]
  congr 1
  exact Finset.sum_congr rfl (fun m _ => smul_iterV E u m (x m))

theorem isSum_cons {x : ℕ → E.M} {s' : E.M} (h : IsSum E (fun m => x (m + 1)) s') :
    IsSum E x (x 0 + E.verschiebung s') := by
  intro N
  cases N with
  | zero => exact ⟨x 0 + E.verschiebung s', by simp⟩
  | succ N =>
    obtain ⟨t, ht⟩ := h N
    exact ⟨t, by rw [ht, peel]⟩

theorem isSum_unique (hc : E.IsVAdicallyComplete) {x : ℕ → E.M} {s s' : E.M}
    (h : IsSum E x s) (h' : IsSum E x s') : s = s' :=
  (hc x).unique h h'

theorem isSum_exists (hc : E.IsVAdicallyComplete) (x : ℕ → E.M) : ∃ s, IsSum E x s :=
  (hc x).exists

theorem isSum_head (hc : E.IsVAdicallyComplete) {x : ℕ → E.M} {s : E.M} (h : IsSum E x s) :
    ∃ s' : E.M, IsSum E (fun m => x (m + 1)) s' ∧ s = x 0 + E.verschiebung s' := by
  obtain ⟨s', hs'⟩ := isSum_exists E hc (fun m => x (m + 1))
  exact ⟨s', hs', isSum_unique E hc h (isSum_cons E hs')⟩

theorem isSum_congr {x x' : ℕ → E.M} {s : E.M} (h : IsSum E x s) (e : ∀ m, x m = x' m) : IsSum E x' s := by
  have : x = x' := funext e
  subst this; exact h

section digits
variable {β : Fin 2 → E.M} (hβ : E.IsHomogeneousVBasis β)

def step (y : E.M) : (Fin 2 → R) × E.M := Classical.choose (hβ.2 y).exists

theorem step_spec (y : E.M) :
    y = (∑ k : Fin 2, WittVector.teichmuller p ((step E hβ y).1 k) • β k) +
      E.verschiebung (step E hβ y).2 :=
  Classical.choose_spec (hβ.2 y).exists

def rest (x : E.M) : ℕ → E.M
  | 0 => x
  | n + 1 => (step E hβ (rest x n)).2

def coef (x : E.M) (n : ℕ) : Fin 2 → R := (step E hβ (rest E hβ x n)).1

theorem rest_zero (x : E.M) : rest E hβ x 0 = x := rfl

theorem rest_succ (x : E.M) (n : ℕ) :
    rest E hβ x n = (∑ k : Fin 2, WittVector.teichmuller p (coef E hβ x n k) • β k) +
      E.verschiebung (rest E hβ x (n + 1)) :=
  step_spec E hβ (rest E hβ x n)

theorem rest_shift (x : E.M) (m : ℕ) : rest E hβ (rest E hβ x 1) m = rest E hβ x (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show (step E hβ (rest E hβ (rest E hβ x 1) m)).2 = (step E hβ (rest E hβ x (m + 1))).2
    rw [ih]

theorem coef_shift (x : E.M) (m : ℕ) : coef E hβ (rest E hβ x 1) m = coef E hβ x (m + 1) := by
  simp only [coef, rest_shift]

theorem isSum_digits (x : E.M) :
    IsSum E (fun m => ∑ k : Fin 2, WittVector.teichmuller p (coef E hβ x m k) • β k) x := by
  intro N
  refine ⟨rest E hβ x N, ?_⟩
  induction N with
  | zero => simp [rest]
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc, Function.iterate_succ_apply, ← iter_add, ← rest_succ]
    exact ih

theorem digit_unique (x : E.M) (t : Fin 2 → R) (x' : E.M)
    (h : x = (∑ k : Fin 2, WittVector.teichmuller p (t k) • β k) + E.verschiebung x') :
    t = coef E hβ x 0 ∧ x' = rest E hβ x 1 := by
  have u := (hβ.2 x).unique (y₁ := (t, x')) (y₂ := (coef E hβ x 0, rest E hβ x 1)) h (rest_succ E hβ x 0)
  exact ⟨congrArg Prod.fst u, congrArg Prod.snd u⟩

end digits

end series

theorem isSum_map {R R' : Type} [CommRing R] [CommRing R'] {jR : Zp2 p →+* R} {jR' : Zp2 p →+* R'}
    (E : GradedCartierModuleData p R jR) (E' : GradedCartierModuleData p R' jR')
    (f : E.M →+ E'.M) (hf : ∀ z, f (E.verschiebung z) = E'.verschiebung (f z))
    {x : ℕ → E.M} {s : E.M} (h : IsSum E x s) : IsSum E' (fun m => f (x m)) (f s) := by
  intro N
  obtain ⟨t, ht⟩ := h N
  refine ⟨f t, ?_⟩
  rw [ht, map_add, map_sum]
  simp only [Function.Semiconj.iterate_right (f := f) (ga := E.verschiebung) (gb := E'.verschiebung) hf _ _]

structure Ctx (p : ℕ) [Fact p.Prime] (S T B' : Type) [CommRing S] [CommRing T] [CommRing B']
    (jS : Zp2 p →+* S) (jT : Zp2 p →+* T) (j' : Zp2 p →+* B') : Type 1 where
  i : S →+* T
  q : T →+* B'
  DS : GradedCartierModuleData p S jS
  DT : GradedCartierModuleData p T jT
  D' : GradedCartierModuleData p B' j'
  g : DS.M →+ DT.M
  k : DS.M →+ D'.M
  γ : Fin 2 → DS.M
  hgs : ∀ (w : WittVector p S) (x : DS.M), g (w • x) = WittVector.map i w • g x
  hgF : ∀ x, g (DS.frobenius x) = DT.frobenius (g x)
  hgV : ∀ x, g (DS.verschiebung x) = DT.verschiebung (g x)
  hks : ∀ (w : WittVector p S) (x : DS.M), k (w • x) = WittVector.map (q.comp i) w • k x
  hkF : ∀ x, k (DS.frobenius x) = D'.frobenius (k x)
  hkV : ∀ x, k (DS.verschiebung x) = D'.verschiebung (k x)
  hγ : DS.IsHomogeneousVBasis γ
  hgγ : DT.IsHomogeneousVBasis (fun i => g (γ i))
  hcS : DS.IsVAdicallyComplete
  hcT : DT.IsVAdicallyComplete
  hc' : D'.IsVAdicallyComplete

namespace Ctx

variable {S T B' : Type} [CommRing S] [CommRing T] [CommRing B']
  {jS : Zp2 p →+* S} {jT : Zp2 p →+* T} {j' : Zp2 p →+* B'}
  (C : Ctx p S T B' jS jT j')

def rowT (w : ℕ → Fin 2 → WittVector p T) (m : ℕ) : C.DT.M := ∑ i : Fin 2, w m i • C.g (C.γ i)
def row' (w : ℕ → Fin 2 → WittVector p T) (m : ℕ) : C.D'.M :=
  ∑ i : Fin 2, WittVector.map C.q (w m i) • C.k (C.γ i)

def Rel (x : C.DT.M) (y : C.D'.M) : Prop :=
  ∃ w : ℕ → Fin 2 → WittVector p T, IsSum C.DT (C.rowT w) x ∧ IsSum C.D' (C.row' w) y

theorem rel_add {x x' : C.DT.M} {y y' : C.D'.M} (h : C.Rel x y) (h' : C.Rel x' y') :
    C.Rel (x + x') (y + y') := by
  obtain ⟨w, hx, hy⟩ := h
  obtain ⟨w', hx', hy'⟩ := h'
  refine ⟨fun m i => w m i + w' m i, ?_, ?_⟩
  · refine isSum_congr C.DT (isSum_add C.DT hx hx') (fun m => ?_)
    simp only [rowT, add_smul, Finset.sum_add_distrib]
  · refine isSum_congr C.D' (isSum_add C.D' hy hy') (fun m => ?_)
    simp only [row', map_add, add_smul, Finset.sum_add_distrib]

theorem rel_smul {x : C.DT.M} {y : C.D'.M} (h : C.Rel x y) (u : WittVector p T) :
    C.Rel (u • x) (WittVector.map C.q u • y) := by
  obtain ⟨w, hx, hy⟩ := h
  refine ⟨fun m i => frobIter m u * w m i, ?_, ?_⟩
  · refine isSum_congr C.DT (isSum_smul C.DT hx u) (fun m => ?_)
    simp only [rowT, Finset.smul_sum, mul_smul]
  · refine isSum_congr C.D' (isSum_smul C.D' hy (WittVector.map C.q u)) (fun m => ?_)
    simp only [row', Finset.smul_sum, map_mul, map_frobIter, mul_smul]

def shiftArr (w : ℕ → Fin 2 → WittVector p T) : ℕ → Fin 2 → WittVector p T
  | 0 => 0
  | m + 1 => w m

theorem rel_V {x : C.DT.M} {y : C.D'.M} (h : C.Rel x y) :
    C.Rel (C.DT.verschiebung x) (C.D'.verschiebung y) := by
  obtain ⟨w, hx, hy⟩ := h
  refine ⟨shiftArr w, ?_, ?_⟩
  · have h0 : C.rowT (shiftArr w) 0 = 0 := by simp [rowT, shiftArr]
    have := isSum_cons C.DT (x := C.rowT (shiftArr w)) (s' := x) hx
    rwa [h0, zero_add] at this
  · have h0 : C.row' (shiftArr w) 0 = 0 := by simp [row', shiftArr]
    have := isSum_cons C.D' (x := C.row' (shiftArr w)) (s' := y) hy
    rwa [h0, zero_add] at this

theorem rel_gk (s : C.DS.M) : C.Rel (C.g s) (C.k s) := by
  refine ⟨fun m i => WittVector.teichmuller p (C.i (coef C.DS C.hγ s m i)), ?_, ?_⟩
  · refine isSum_congr C.DT (isSum_map C.DS C.DT C.g C.hgV (isSum_digits C.DS C.hγ s)) (fun m => ?_)
    simp only [rowT, map_sum, C.hgs, WittVector.map_teichmuller]
  · refine isSum_congr C.D' (isSum_map C.DS C.D' C.k C.hkV (isSum_digits C.DS C.hγ s)) (fun m => ?_)
    simp only [row', map_sum, C.hks, WittVector.map_teichmuller, RingHom.comp_apply]

theorem rel_sum2 {a : Fin 2 → C.DT.M} {b : Fin 2 → C.D'.M} (h : ∀ i, C.Rel (a i) (b i)) :
    C.Rel (∑ i : Fin 2, a i) (∑ i : Fin 2, b i) := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  exact C.rel_add (h 0) (h 1)

theorem key {x : C.DT.M} {y : C.D'.M} (h : C.Rel x y) :
    ∃ (t : Fin 2 → T) (x' : C.DT.M) (y' : C.D'.M), C.Rel x' y' ∧
      x = (∑ i : Fin 2, WittVector.teichmuller p (t i) • C.g (C.γ i)) + C.DT.verschiebung x' ∧
      y = (∑ i : Fin 2, WittVector.teichmuller p (C.q (t i)) • C.k (C.γ i)) + C.D'.verschiebung y' := by
  obtain ⟨w, hx, hy⟩ := h
  obtain ⟨x₁, hx₁, ex⟩ := isSum_head C.DT C.hcT hx
  obtain ⟨y₁, hy₁, ey⟩ := isSum_head C.D' C.hc' hy
  have hrel₁ : C.Rel x₁ y₁ := ⟨fun m => w (m + 1), hx₁, hy₁⟩
  choose t u' hw using fun i => witt_split (w 0 i)
  have hrelF : ∀ i : Fin 2, C.Rel (u' i • C.g (C.DS.frobenius (C.γ i)))
      (WittVector.map C.q (u' i) • C.k (C.DS.frobenius (C.γ i))) :=
    fun i => C.rel_smul (C.rel_gk _) _
  refine ⟨t, x₁ + ∑ i : Fin 2, u' i • C.g (C.DS.frobenius (C.γ i)),
    y₁ + ∑ i : Fin 2, WittVector.map C.q (u' i) • C.k (C.DS.frobenius (C.γ i)),
    C.rel_add hrel₁ (C.rel_sum2 hrelF), ?_, ?_⟩
  · have e0 : ∀ i : Fin 2, w 0 i • C.g (C.γ i) = WittVector.teichmuller p (t i) • C.g (C.γ i) +
        C.DT.verschiebung (u' i • C.g (C.DS.frobenius (C.γ i))) := fun i => by
      rw [hw i, add_smul, C.hgF, C.DT.verschiebung_smul_frobenius]
    rw [ex]
    simp only [rowT, Fin.sum_univ_two, e0, map_add]
    abel
  · have e0 : ∀ i : Fin 2, WittVector.map C.q (w 0 i) • C.k (C.γ i) =
        WittVector.teichmuller p (C.q (t i)) • C.k (C.γ i) +
        C.D'.verschiebung (WittVector.map C.q (u' i) • C.k (C.DS.frobenius (C.γ i))) := fun i => by
      rw [hw i, map_add, WittVector.map_teichmuller, WittVector.map_verschiebung, add_smul, C.hkF,
        C.D'.verschiebung_smul_frobenius]
    rw [ey]
    simp only [row', Fin.sum_univ_two, e0, map_add]
    abel

def dser (x : C.DT.M) (m : ℕ) : C.D'.M :=
  ∑ i : Fin 2, WittVector.teichmuller p (C.q (coef C.DT C.hgγ x m i)) • C.k (C.γ i)

theorem sync (N : ℕ) : ∀ (x : C.DT.M) (y : C.D'.M), C.Rel x y →
    ∃ y' : C.D'.M, C.Rel (rest C.DT C.hgγ x N) y' ∧
      y = (∑ m ∈ Finset.range N, (⇑C.D'.verschiebung)^[m] (C.dser x m)) + (⇑C.D'.verschiebung)^[N] y' := by
  induction N with
  | zero => intro x y h; exact ⟨y, h, by simp [rest]⟩
  | succ N ih =>
    intro x y h
    obtain ⟨t, x', y', hrel, ex, ey⟩ := C.key h
    obtain ⟨ht, hx'⟩ := digit_unique C.DT C.hgγ x t x' ex
    subst ht hx'
    obtain ⟨y'', hrel'', ey'⟩ := ih _ _ hrel
    refine ⟨y'', by rwa [rest_shift] at hrel'', ?_⟩
    rw [ey, ey']
    simp only [dser, coef_shift]
    exact peel C.D' (fun m => ∑ i : Fin 2,
      WittVector.teichmuller p (C.q (coef C.DT C.hgγ x m i)) • C.k (C.γ i)) N y''

theorem isSum_dser {x : C.DT.M} {y : C.D'.M} (h : C.Rel x y) : IsSum C.D' (C.dser x) y := by
  intro N
  obtain ⟨y', -, e⟩ := C.sync N x y h
  exact ⟨y', e⟩

def H (x : C.DT.M) : C.D'.M := Classical.choose (isSum_exists C.D' C.hc' (C.dser x))

theorem H_spec (x : C.DT.M) : IsSum C.D' (C.dser x) (C.H x) :=
  Classical.choose_spec (isSum_exists C.D' C.hc' (C.dser x))

theorem rel_eq {x : C.DT.M} {y : C.D'.M} (h : C.Rel x y) : y = C.H x :=
  isSum_unique C.D' C.hc' (C.isSum_dser h) (C.H_spec x)

theorem rel_H (x : C.DT.M) : C.Rel x (C.H x) := by
  refine ⟨fun m i => WittVector.teichmuller p (coef C.DT C.hgγ x m i), ?_, ?_⟩
  · exact isSum_congr C.DT (isSum_digits C.DT C.hgγ x) (fun m => rfl)
  · refine isSum_congr C.D' (C.H_spec x) (fun m => ?_)
    simp only [row', dser, WittVector.map_teichmuller]

theorem H_add (x x' : C.DT.M) : C.H (x + x') = C.H x + C.H x' :=
  (C.rel_eq (C.rel_add (C.rel_H x) (C.rel_H x'))).symm

theorem H_smul (u : WittVector p T) (x : C.DT.M) : C.H (u • x) = WittVector.map C.q u • C.H x :=
  (C.rel_eq (C.rel_smul (C.rel_H x) u)).symm

theorem H_V (x : C.DT.M) : C.H (C.DT.verschiebung x) = C.D'.verschiebung (C.H x) :=
  (C.rel_eq (C.rel_V (C.rel_H x))).symm

theorem H_g (s : C.DS.M) : C.H (C.g s) = C.k s :=
  (C.rel_eq (C.rel_gk s)).symm

def Hhom : C.DT.M →+ C.D'.M := AddMonoidHom.mk' C.H C.H_add

end Ctx

end P2mBce

end

open P2mBce in
theorem solution
    (p : ℕ) [Fact p.Prime] {S T B' : Type} [CommRing S] [CommRing T] [CommRing B']
    {jS : CerednikDrinfeld.Zp2 p →+* S} {jT : CerednikDrinfeld.Zp2 p →+* T}
    {j' : CerednikDrinfeld.Zp2 p →+* B'}
    (i : S →+* T) (q : T →+* B')
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule)
    (DT : CerednikDrinfeld.GradedCartierModuleData p T jT) (hDT : DT.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (g : DS.M →+ DT.M) (hg : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' i DS DT g)
    (k : DS.M →+ D'.M) (hk : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' (q.comp i) DS D' k)
    (γ : Fin 2 → DS.M) (hγ : DS.IsHomogeneousVBasis γ) (hgγ : DT.IsHomogeneousVBasis (fun i => g (γ i))) :
    ∃ h : DT.M →+ D'.M,
      (∀ (w : WittVector p T) (x : DT.M), h (w • x) = WittVector.map q w • h x) ∧
      (∀ x : DT.M, h (DT.verschiebung x) = D'.verschiebung (h x)) ∧
      ∀ i : Fin 2, h (g (γ i)) = k (γ i) := by
  let C : P2mBce.Ctx p S T B' jS jT j' :=
    { i := i, q := q, DS := DS, DT := DT, D' := D', g := g, k := k, γ := γ,
      hgs := hg.1, hgF := hg.2.1, hgV := hg.2.2.1, hks := hk.1, hkF := hk.2.1, hkV := hk.2.2.1,
      hγ := hγ, hgγ := hgγ, hcS := hDS.2, hcT := hDT.2, hc' := hD'.2 }
  exact ⟨C.Hhom, fun w x => C.H_smul w x, fun x => C.H_V x, fun i => C.H_g (γ i)⟩

end S_CerednikDrinfeld_GradedCartierModuleData_exists_map_smul_map_verschiebung_apply_basis_eq_of_baseChange
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_map_smul_map_verschiebung_apply_basis_eq_of_baseChange (solution)
