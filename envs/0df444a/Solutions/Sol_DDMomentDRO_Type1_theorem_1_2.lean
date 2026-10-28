-- Prove2me | solution 2 for DDMomentDRO.Type1.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T06:25:55.700356+00:00
-- url     : https://prove2.me/submissions/f1128701-20eb-48ee-a11f-0d75050c9bf3

import Mathlib
import Definitions.Def_DDMomentDRO_Type1_Setting
import Theorems.Thm_LP_farkas
import Theorems.Thm_MinMax_isLeast_add_isGreatest_iff

-- carved verbatim out of submission f67f307e-921d-4122-82bb-a74f3a3cb9f1, lines 837-875

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def LP.Feas (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ) : Set E :=
  {x | (∀ i, a i x ≤ b i) ∧ ∀ j, e j x = d j}

def LP.DualFeas (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    Set ((ι → ℝ) × (κ → ℝ)) :=
  {yz | 0 ≤ yz.1 ∧ ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j = c}

theorem LP.weak_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) {x : E} (hx : x ∈ LP.Feas a b e d)
    {yz : (ι → ℝ) × (κ → ℝ)} (hyz : yz ∈ LP.DualFeas a e c) :
    c x ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d := by
  obtain ⟨hax, hex⟩ := hx
  obtain ⟨hy, hsum⟩ := hyz
  have h := congrArg (fun φ : Module.Dual ℝ E => φ x) hsum
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hex] at h
  have hle : ∑ i, yz.1 i * a i x ≤ ∑ i, yz.1 i * b i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hax i) (hy i)
  simp only [dotProduct]
  linarith

lemma aux1_alt (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty) (t : ℝ)
    (h : ∀ x ∈ LP.Feas a b e d, c x < t) :
    ∃ yz ∈ LP.DualFeas a e c, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d < t := by
  classical
  let a' : Option ι → Module.Dual ℝ E := fun o => o.elim (-c) a
  let b' : Option ι → ℝ := fun o => o.elim (-t) b
  have hinf : ¬ ∃ x : E, (∀ i, a' i x ≤ b' i) ∧ ∀ j, e j x = d j := by
    rintro ⟨x, hx1, hx2⟩
    have h1 := h x ⟨fun i => hx1 (some i), hx2⟩
    have h2 := hx1 none
    simp only [a', b', Option.elim, LinearMap.neg_apply] at h2
    linarith
  obtain ⟨y', z, hy', hsum, hneg⟩ := (LP.farkas a' b' e d).1 hinf
  rw [Fintype.sum_option] at hsum
  simp only [dotProduct, Fintype.sum_option] at hneg
  simp only [a', b', Option.elim, smul_neg] at hsum hneg
  have hy0 : 0 ≤ y' none := hy' none
  rcases hy0.eq_or_lt with h0 | h0
  · exfalso
    obtain ⟨x0, hx0⟩ := hP
    refine (LP.farkas a b e d).2 ⟨fun i => y' (some i), z, fun i => hy' (some i), ?_, ?_⟩
      ⟨x0, hx0⟩
    · rw [← h0] at hsum; simpa using hsum
    · simp only [dotProduct]; rw [← h0] at hneg; simpa using hneg
  · refine ⟨(fun i => y' (some i) / y' none, fun j => z j / y' none),
      ⟨fun i => div_nonneg (hy' _) h0.le, ?_⟩, ?_⟩
    · have hAB : ∑ i, y' (some i) • a i + ∑ j, z j • e j = y' none • c := by
        rw [← sub_eq_zero, ← hsum]; abel
      show ∑ i, (y' (some i) / y' none) • a i + ∑ j, (z j / y' none) • e j = c
      have hr : ∀ (r : ℝ) (φ : Module.Dual ℝ E), (r / y' none) • φ = (y' none)⁻¹ • (r • φ) :=
        fun r φ => by rw [smul_smul, div_eq_inv_mul]
      simp only [hr]
      rw [← Finset.smul_sum, ← Finset.smul_sum, ← smul_add, hAB, smul_smul,
        inv_mul_cancel₀ h0.ne', one_smul]
    · simp only [dotProduct]
      have : ∑ i, y' (some i) / y' none * b i + ∑ j, z j / y' none * d j =
          (∑ i, y' (some i) * b i + ∑ j, z j * d j) / y' none := by
        rw [add_div, Finset.sum_div, Finset.sum_div]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this, div_lt_iff₀ h0]
      linarith

lemma aux1_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) :
    ∃ x ∈ LP.Feas a b e d, ∀ x' ∈ LP.Feas a b e d, c x' ≤ c x := by
  by_contra hno
  push Not at hno
  have hlt : ∀ x ∈ LP.Feas a b e d, c x < sSup (c '' LP.Feas a b e d) := fun x hx => by
    obtain ⟨x', hx', hlt⟩ := hno x hx
    exact lt_of_lt_of_le hlt (le_csSup hb ⟨x', hx', rfl⟩)
  obtain ⟨yz, hyz, hobj⟩ := aux1_alt a b e d c hP _ hlt
  have : sSup (c '' LP.Feas a b e d) ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d :=
    csSup_le (hP.image c) (by rintro _ ⟨x, hx, rfl⟩; exact LP.weak_duality a b e d c hx hyz)
  linarith

def aux1_T (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) :
    (ι → ℝ) × (κ → ℝ) →ₗ[ℝ] Module.Dual ℝ E where
  toFun yz := ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

def aux1_obj (b : ι → ℝ) (d : κ → ℝ) : Module.Dual ℝ ((ι → ℝ) × (κ → ℝ)) where
  toFun yz := yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct]; ring
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring

lemma aux1_dualFeas_eq (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    LP.DualFeas a e c =
      LP.Feas (fun i => -(LinearMap.proj i ∘ₗ LinearMap.fst ℝ (ι → ℝ) (κ → ℝ))) 0
        (fun k => Module.Dual.eval ℝ E (Module.finBasis ℝ E k) ∘ₗ aux1_T a e)
        (fun k => c (Module.finBasis ℝ E k)) := by
  ext yz
  simp only [LP.DualFeas, LP.Feas, Set.mem_setOf_eq, LinearMap.neg_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_fst, LinearMap.coe_proj, Function.eval, Pi.zero_apply,
    neg_nonpos, Module.Dual.eval_apply]
  constructor
  · rintro ⟨hy, hsum⟩
    exact ⟨fun i => hy i, fun k => by rw [← hsum]; rfl⟩
  · rintro ⟨hy, hk⟩
    refine ⟨fun i => hy i, ?_⟩
    have : aux1_T a e yz = c := (Module.finBasis ℝ E).ext fun k => hk k
    exact this

lemma aux1_dual_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E)
    (d : κ → ℝ) (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ yz ∈ LP.DualFeas a e c, ∀ yz' ∈ LP.DualFeas a e c,
      yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ yz'.1 ⬝ᵥ b + yz'.2 ⬝ᵥ d := by
  obtain ⟨x0, hx0⟩ := hP
  rw [aux1_dualFeas_eq] at hD ⊢
  obtain ⟨yz, hyz, hmax⟩ := aux1_attain _ _ _ _ (-aux1_obj b d) hD (by
    refine ⟨-c x0, ?_⟩
    rintro _ ⟨yz', hyz', rfl⟩
    rw [← aux1_dualFeas_eq] at hyz'
    have := LP.weak_duality a b e d c hx0 hyz'
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    exact this)
  refine ⟨yz, hyz, fun yz' hyz' => ?_⟩
  have := hmax yz' hyz'
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  exact this

theorem LP.strong_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ v : ℝ, IsGreatest (c '' LP.Feas a b e d) v ∧
      IsLeast ((fun yz => yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d) '' LP.DualFeas a e c) v := by
  obtain ⟨yz, hyz, hmin⟩ := aux1_dual_attain a b e d c hP hD
  obtain ⟨x, hx, hxw⟩ : ∃ x ∈ LP.Feas a b e d, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ c x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨yz', hyz', hlt⟩ := aux1_alt a b e d c hP _ hcon
    linarith [hmin yz' hyz']
  refine ⟨yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d,
    ⟨⟨x, hx, le_antisymm (LP.weak_duality a b e d c hx hyz) hxw⟩, ?_⟩,
    ⟨⟨yz, hyz, rfl⟩, ?_⟩⟩
  · rintro _ ⟨x', hx', rfl⟩; exact LP.weak_duality a b e d c hx' hyz
  · rintro _ ⟨yz', hyz', rfl⟩; exact hmin yz' hyz'

end

section
open Matrix
variable {K m : ℕ}

def lf (w : Fin K → ℝ) : Module.Dual ℝ (Fin K → ℝ) where
  toFun p := w ⬝ᵥ p
  map_add' p q := dotProduct_add w p q
  map_smul' c p := by simp [dotProduct_smul]

@[simp] lemma lf_apply (w p : Fin K → ℝ) : lf w p = w ⬝ᵥ p := rfl

lemma sum_smul_lf {ι : Type*} [Fintype ι] (y : ι → ℝ) (w : ι → Fin K → ℝ) :
    ∑ i, y i • lf (w i) = lf (∑ i, y i • w i) := by
  refine LinearMap.ext fun p => ?_
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, lf_apply, smul_eq_mul, dotProduct, Finset.sum_apply,
    Pi.smul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

lemma lf_inj {w w' : Fin K → ℝ} (h : lf w = lf w') : w = w' := by
  funext k
  have := congrArg (fun φ => φ (Pi.single k 1)) h
  simpa [dotProduct_single] using this

abbrev Idx (K m : ℕ) := Fin K ⊕ Fin K ⊕ Fin m ⊕ Fin m ⊕ Fin K

def wv (F : Fin K → Fin m → ℝ) : Idx K m → Fin K → ℝ
  | .inl k => -Pi.single k 1
  | .inr (.inl k) => Pi.single k 1
  | .inr (.inr (.inl s)) => -(fun k => F k s)
  | .inr (.inr (.inr (.inl s))) => fun k => F k s
  | .inr (.inr (.inr (.inr k))) => -Pi.single k 1

def bv (lo hi : Fin m → ℝ) (pL pU : Fin K → ℝ) : Idx K m → ℝ
  | .inl k => -pL k
  | .inr (.inl k) => pU k
  | .inr (.inr (.inl s)) => -lo s
  | .inr (.inr (.inr (.inl s))) => hi s
  | .inr (.inr (.inr (.inr _))) => 0

lemma mom_eq (F : Fin K → Fin m → ℝ) (p : Fin K → ℝ) (s : Fin m) :
    (fun k => F k s) ⬝ᵥ p = (∑ k, p k • F k) s := by
  simp [dotProduct, Finset.sum_apply, mul_comm]

lemma feas_iff (F : Fin K → Fin m → ℝ) (lo hi : Fin m → ℝ) (pL pU : Fin K → ℝ)
    (p : Fin K → ℝ) :
    p ∈ LP.Feas (fun i => lf (wv F i)) (bv lo hi pL pU)
        (fun j : Empty => j.elim) (fun j => j.elim) ↔
      (pL ≤ p ∧ p ≤ pU ∧ lo ≤ ∑ k, p k • F k ∧ ∑ k, p k • F k ≤ hi ∧ ∀ k, 0 ≤ p k) := by
  constructor
  · rintro ⟨h, -⟩
    refine ⟨fun k => ?_, fun k => ?_, fun s => ?_, fun s => ?_, fun k => ?_⟩
    · have := h (.inl k); simp [wv, bv] at this; linarith
    · have := h (.inr (.inl k)); simpa [wv, bv] using this
    · have := h (.inr (.inr (.inl s))); simp only [lf_apply, wv, bv, neg_dotProduct,
        mom_eq] at this; linarith
    · have := h (.inr (.inr (.inr (.inl s)))); simp only [lf_apply, wv, bv, mom_eq] at this
      exact this
    · have := h (.inr (.inr (.inr (.inr k)))); simp [wv, bv] at this; linarith
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨?_, fun j => j.elim⟩
    rintro (k | k | s | s | k)
    · simp [wv, bv]; exact h1 k
    · simpa [wv, bv] using h2 k
    · simp only [lf_apply, wv, bv, neg_dotProduct, mom_eq]; linarith [h3 s]
    · simp only [lf_apply, wv, bv, mom_eq]; exact h4 s
    · simp [wv, bv]; exact h5 k

lemma sum_wv (F : Fin K → Fin m → ℝ) (y : Idx K m → ℝ) (k : Fin K) :
    (∑ i, y i • wv F i) k = -y (.inl k) + y (.inr (.inl k))
      - ∑ s, y (.inr (.inr (.inl s))) * F k s + ∑ s, y (.inr (.inr (.inr (.inl s)))) * F k s
      - y (.inr (.inr (.inr (.inr k)))) := by
  simp [Finset.sum_apply, Fintype.sum_sum_type, wv, Pi.single_apply, Finset.sum_neg_distrib]
  ring

lemma obj_eq (lo hi : Fin m → ℝ) (pL pU : Fin K → ℝ) (y : Idx K m → ℝ) :
    y ⬝ᵥ bv lo hi pL pU = -((fun s => y (.inr (.inr (.inl s)))) ⬝ᵥ lo)
      + (fun s => y (.inr (.inr (.inr (.inl s))))) ⬝ᵥ hi
      - (fun k => y (.inl k)) ⬝ᵥ pL + (fun k => y (.inr (.inl k))) ⬝ᵥ pU := by
  simp [dotProduct, Fintype.sum_sum_type, bv, Finset.sum_neg_distrib]
  ring

lemma dot_empty (z w : Empty → ℝ) : z ⬝ᵥ w = 0 := by simp [dotProduct]

lemma dualfeas_iff (F : Fin K → Fin m → ℝ) (Q : Fin K → ℝ)
    (yz : (Idx K m → ℝ) × (Empty → ℝ)) :
    yz ∈ LP.DualFeas (fun i => lf (wv F i)) (fun j : Empty => j.elim) (lf Q) ↔
      0 ≤ yz.1 ∧ ∀ k, -yz.1 (.inl k) + yz.1 (.inr (.inl k))
      - ∑ s, yz.1 (.inr (.inr (.inl s))) * F k s + ∑ s, yz.1 (.inr (.inr (.inr (.inl s)))) * F k s
      - yz.1 (.inr (.inr (.inr (.inr k)))) = Q k := by
  unfold LP.DualFeas
  simp only [Set.mem_setOf_eq, Finset.univ_eq_empty, Finset.sum_empty, add_zero, sum_smul_lf]
  refine and_congr Iff.rfl ⟨fun h k => ?_, fun h => ?_⟩
  · rw [← sum_wv, lf_inj h]
  · congr 1; funext k; rw [sum_wv, h k]

lemma pointwise (F : Fin K → Fin m → ℝ) (Q : Fin K → ℝ) (lo hi : Fin m → ℝ)
    (pL pU : Fin K → ℝ)
    (hne : {p : Fin K → ℝ | pL ≤ p ∧ p ≤ pU ∧ lo ≤ ∑ k, p k • F k ∧ ∑ k, p k • F k ≤ hi ∧
      ∀ k, 0 ≤ p k}.Nonempty) :
    ∃ w, IsGreatest {v | ∃ p : Fin K → ℝ, (pL ≤ p ∧ p ≤ pU ∧ lo ≤ ∑ k, p k • F k ∧
        ∑ k, p k • F k ≤ hi ∧ ∀ k, 0 ≤ p k) ∧ v = ∑ k, p k * Q k} w ∧
      IsLeast {d | ∃ (α β : Fin m → ℝ) (γl γu : Fin K → ℝ),
        (0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γl ∧ 0 ≤ γu ∧ ∀ k, Q k ≤ (β - α) ⬝ᵥ F k - γl k + γu k) ∧
        d = -(α ⬝ᵥ lo) + β ⬝ᵥ hi - γl ⬝ᵥ pL + γu ⬝ᵥ pU} w := by
  have hP : (LP.Feas (fun i => lf (wv F i)) (bv lo hi pL pU)
      (fun j : Empty => j.elim) (fun j => j.elim)).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, (feas_iff F lo hi pL pU p).2 hp⟩
  -- dual point from dual-feasible quadruple
  have hmk : ∀ (α β : Fin m → ℝ) (γl γu : Fin K → ℝ),
      (0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γl ∧ 0 ≤ γu ∧ ∀ k, Q k ≤ (β - α) ⬝ᵥ F k - γl k + γu k) →
      ∃ yz ∈ LP.DualFeas (fun i => lf (wv F i)) (fun j : Empty => j.elim) (lf Q),
        yz.1 ⬝ᵥ bv lo hi pL pU + yz.2 ⬝ᵥ (fun j : Empty => j.elim) =
          -(α ⬝ᵥ lo) + β ⬝ᵥ hi - γl ⬝ᵥ pL + γu ⬝ᵥ pU := by
    rintro α β γl γu ⟨hα, hβ, hγl, hγu, hk⟩
    let y : Idx K m → ℝ := fun i => match i with
      | .inl k => γl k
      | .inr (.inl k) => γu k
      | .inr (.inr (.inl s)) => α s
      | .inr (.inr (.inr (.inl s))) => β s
      | .inr (.inr (.inr (.inr k))) => (β - α) ⬝ᵥ F k - γl k + γu k - Q k
    refine ⟨(y, fun j => j.elim), (dualfeas_iff F Q _).2 ⟨?_, fun k => ?_⟩, ?_⟩
    · rintro (k | k | s | s | k)
      · exact hγl k
      · exact hγu k
      · exact hα s
      · exact hβ s
      · show (0 : ℝ) ≤ (β - α) ⬝ᵥ F k - γl k + γu k - Q k
        linarith [hk k]
    · show -γl k + γu k - ∑ s, α s * F k s + ∑ s, β s * F k s
        - ((β - α) ⬝ᵥ F k - γl k + γu k - Q k) = Q k
      simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      ring
    · rw [dot_empty, add_zero, obj_eq]

  have hD : (LP.DualFeas (fun i => lf (wv F i)) (fun j : Empty => j.elim)
      (lf Q)).Nonempty := by
    obtain ⟨yz, hyz, -⟩ := hmk 0 0 0 (fun k => max (Q k) 0)
      ⟨le_rfl, le_rfl, le_rfl, fun k => le_max_right _ _, fun k => by simp⟩
    exact ⟨yz, hyz⟩
  obtain ⟨v, hG, hL⟩ := LP.strong_duality (fun i => lf (wv F i)) (bv lo hi pL pU)
    (fun j : Empty => j.elim) (fun j => j.elim) (lf Q) hP hD
  refine ⟨v, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨p, hp, hv⟩ := hG.1
    refine ⟨p, (feas_iff F lo hi pL pU p).1 hp, ?_⟩
    rw [← hv]; simp [dotProduct, mul_comm]
  · rintro _ ⟨p, hp, rfl⟩
    have := hG.2 ⟨p, (feas_iff F lo hi pL pU p).2 hp, rfl⟩
    simpa [dotProduct, mul_comm] using this
  · obtain ⟨yz, hyz, hv⟩ := hL.1
    obtain ⟨hy, hk⟩ := (dualfeas_iff F Q yz).1 hyz
    refine ⟨fun s => yz.1 (.inr (.inr (.inl s))), fun s => yz.1 (.inr (.inr (.inr (.inl s)))),
      fun k => yz.1 (.inl k), fun k => yz.1 (.inr (.inl k)),
      ⟨fun s => hy _, fun s => hy _, fun k => hy _, fun k => hy _, fun k => ?_⟩, ?_⟩
    · have h1 := hk k
      have h2 := hy (.inr (.inr (.inr (.inr k))))
      simp only [Pi.zero_apply] at h2
      simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      linarith
    · rw [← hv]
      beta_reduce
      rw [dot_empty, add_zero, obj_eq]
  · rintro _ ⟨α, β, γl, γu, hF, rfl⟩
    obtain ⟨yz, hyz, hobj⟩ := hmk α β γl γu hF
    rw [← hobj]
    exact hL.2 ⟨yz, hyz, rfl⟩

end

section

open DDMomentDRO.Type1 in
theorem solution {I J K m : ℕ}
    (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ)
    (hbin : ∀ p ∈ S, ∀ i, p.1 i = 0 ∨ p.1 i = 1)
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ) (e : Fin m → Fin J → ℕ)
    (l u : (Fin I → ℝ) → Fin m → ℝ) (pl pu : (Fin I → ℝ) → Fin K → ℝ)
    (hne : ∀ x y, (x, y) ∈ S → (amb1 ξ e l u pl pu x).Nonempty) :
    ∀ q : ℝ, IsLeast (stageVals S g (amb1 ξ e l u pl pu) Qn) q ↔
      IsLeast (dualVals1 S g Qn ξ e l u pl pu) q := by
  intro q
  have key := MinMax.isLeast_add_isGreatest_iff S (fun z => g z.1 z.2)
    (fun z => wcVal (amb1 ξ e l u pl pu) Qn z.1)
    (fun z => {d | ∃ α β γl γu, DualFeas1 Qn ξ e z.1 α β γl γu ∧
      d = dualObj1 l u pl pu z.1 α β γl γu})
    (fun z hz => pointwise (fun k => momentFn e (ξ k))
      (Qn z.1) (l z.1) (u z.1) (pl z.1) (pu z.1) (hne z.1 z.2 hz)) q
  have e1 : stageVals S g (amb1 ξ e l u pl pu) Qn =
      {v | ∃ z ∈ S, ∃ w, IsGreatest (wcVal (amb1 ξ e l u pl pu) Qn z.1) w ∧
        v = g z.1 z.2 + w} := by
    ext v
    constructor
    · rintro ⟨x, y, w, hS, hw, rfl⟩
      exact ⟨(x, y), hS, w, hw, rfl⟩
    · rintro ⟨⟨x, y⟩, hS, w, hw, rfl⟩
      exact ⟨x, y, w, hS, hw, rfl⟩
  have e2 : dualVals1 S g Qn ξ e l u pl pu =
      {v | ∃ z ∈ S, ∃ d ∈ {d | ∃ α β γl γu, DualFeas1 Qn ξ e z.1 α β γl γu ∧
        d = dualObj1 l u pl pu z.1 α β γl γu}, v = g z.1 z.2 + d} := by
    ext v
    constructor
    · rintro ⟨x, y, α, β, γl, γu, hS, hF, rfl⟩
      exact ⟨(x, y), hS, _, ⟨α, β, γl, γu, hF, rfl⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, hS, d, ⟨α, β, γl, γu, hF, rfl⟩, rfl⟩
      exact ⟨x, y, α, β, γl, γu, hS, hF, rfl⟩
  rw [e1, e2]
  exact key

end
