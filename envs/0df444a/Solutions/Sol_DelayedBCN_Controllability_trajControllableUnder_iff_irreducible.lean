-- Prove2me | solution 1 for DelayedBCN.Controllability.trajControllableUnder_iff_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T03:33:09.772874+00:00
-- url     : https://prove2.me/submissions/e0a1154a-bea4-4804-be6f-0af5362505c8

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix

set_option autoImplicit false

open DelayedBCN.Controllability in
private lemma f3ed_trajAt_succ {μ n m k : ℕ} (F : Network μ n m) (X0 : Traj μ n)
    (U : Fin k → Input m) (i : ℕ) (hi : i < k) :
    trajAt F X0 U (i + 1) = step F (U ⟨i, hi⟩) (trajAt F X0 U i) := by
  simp only [trajAt, dif_pos hi]

open DelayedBCN.Controllability in
private lemma f3ed_trajAt_snoc {μ n m k : ℕ} (F : Network μ n m) (X0 : Traj μ n)
    (U : Fin k → Input m) (u : Input m) :
    ∀ i, i ≤ k → trajAt F X0 (Fin.snoc U u : Fin (k + 1) → Input m) i = trajAt F X0 U i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hik : i < k := hi
    rw [f3ed_trajAt_succ F X0 _ i (by omega), f3ed_trajAt_succ F X0 U i hik, ih (by omega)]
    congr 1
    have : (⟨i, by omega⟩ : Fin (k + 1)) = Fin.castSucc ⟨i, hik⟩ := rfl
    rw [this, Fin.snoc_castSucc]

open DelayedBCN.Controllability in
private lemma f3ed_trajAt_snoc_last {μ n m k : ℕ} (F : Network μ n m) (X0 : Traj μ n)
    (U : Fin k → Input m) (u : Input m) :
    trajAt F X0 (Fin.snoc U u : Fin (k + 1) → Input m) (k + 1) = step F u (trajAt F X0 U k) := by
  rw [f3ed_trajAt_succ F X0 _ k (by omega), f3ed_trajAt_snoc F X0 U u k le_rfl]
  congr 1
  have : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := rfl
  rw [this, Fin.snoc_last]

open DelayedBCN.Controllability in
private lemma f3ed_extend {μ n m : ℕ} (F : Network μ n m) (Ct : Finset (Traj μ n))
    (a x y : Traj μ n) (u : Input m) (hy : y ∉ Ct) (hxy : step F u x = y)
    (h : ∃ k : ℕ, ∃ U : Fin k → Input m, SteersAvoiding F a x Ct U) :
    ∃ k : ℕ, ∃ U : Fin k → Input m, SteersAvoiding F a y Ct U := by
  simp only [SteersAvoiding] at h ⊢
  obtain ⟨k, U, hU1, hU2⟩ := h
  refine ⟨k + 1, Fin.snoc U u, ?_, ?_⟩
  · rw [f3ed_trajAt_snoc_last, hU1, hxy]
  · intro i
    by_cases hi : i.val ≤ k
    · rw [f3ed_trajAt_snoc F a U u i.val hi]
      exact hU2 ⟨i.val, by omega⟩
    · have : i.val = k + 1 := by omega
      rw [this, f3ed_trajAt_snoc_last, hU1, hxy]
      exact hy

open DelayedBCN.Controllability in
private lemma f3ed_Q_pos {μ n m : ℕ} (F : Network μ n m) (Ct : Finset (Traj μ n))
    (x y : {a : Traj μ n // a ∉ Ct}) (u : Input m) (h : step F u x.1 = y.1) :
    (QDeleted F Ct).map (fun t : ℕ => (t : ℝ)) y x ≠ 0 := by
  simp only [Matrix.map_apply, QDeleted, Q, Nat.cast_ne_zero]
  rw [← Nat.pos_iff_ne_zero, Finset.card_pos]
  exact ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

open DelayedBCN.Controllability in
private lemma f3ed_Q_ne {μ n m : ℕ} (F : Network μ n m) (Ct : Finset (Traj μ n))
    (x y : {a : Traj μ n // a ∉ Ct})
    (h : (QDeleted F Ct).map (fun t : ℕ => (t : ℝ)) y x ≠ 0) : ∃ u, step F u x.1 = y.1 := by
  simp only [Matrix.map_apply, QDeleted, Q, Nat.cast_ne_zero] at h
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h)
  exact ⟨u, (Finset.mem_filter.1 hu).2⟩

open DelayedBCN.Controllability in
private lemma f3ed_reducible_of_closed {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (p : ι → Prop) (a b : ι) (ha : p a) (hb : ¬ p b)
    (hcl : ∀ x y, p x → ¬ p y → A y x = 0) : IsReducibleMat A := by
  classical
  have hrs : Fintype.card {x // p x} + Fintype.card {x // ¬ p x} = Fintype.card ι := by
    rw [← Fintype.card_sum]; exact Fintype.card_congr (Equiv.sumCompl p)
  have hr1 : 1 ≤ Fintype.card {x // p x} := Fintype.card_pos_iff.2 ⟨⟨a, ha⟩⟩
  have hs1 : 1 ≤ Fintype.card {x // ¬ p x} := Fintype.card_pos_iff.2 ⟨⟨b, hb⟩⟩
  set r := Fintype.card {x // p x} with hr
  set s := Fintype.card {x // ¬ p x} with hs
  let e1 : Fin (Fintype.card ι) ≃ Fin (r + s) := finCongr hrs.symm
  let e2 : Fin (r + s) ≃ Fin r ⊕ Fin s := finSumFinEquiv.symm
  let e3 : Fin r ⊕ Fin s ≃ {x // p x} ⊕ {x // ¬ p x} :=
    Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm
  let e4 : {x // p x} ⊕ {x // ¬ p x} ≃ ι := Equiv.sumCompl p
  let e : Fin (Fintype.card ι) ≃ ι := e1.trans (e2.trans (e3.trans e4))
  have hkey : ∀ j : Fin (Fintype.card ι), (p (e j) ↔ j.val < r) := by
    intro j
    have hej : e j = e4 (e3 (e2 (e1 j))) := rfl
    have hv : (e1 j).val = j.val := rfl
    obtain ⟨z, hz⟩ : ∃ z, e2 (e1 j) = z := ⟨_, rfl⟩
    have hz' : e1 j = finSumFinEquiv z := by rw [← hz]; simp [e2]
    rcases z with y | y
    · have hjv : j.val = y.val := by rw [← hv, hz']; simp
      rw [hej, hz]
      simp only [e3, e4, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
      exact ⟨fun _ => by omega, fun _ => ((Fintype.equivFin {x // p x}).symm y).2⟩
    · have hjv : j.val = r + y.val := by rw [← hv, hz']; simp
      rw [hej, hz]
      simp only [e3, e4, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
      exact ⟨fun h => absurd h ((Fintype.equivFin {x // ¬ p x}).symm y).2, fun h => by omega⟩
  refine ⟨e, r, hr1, by omega, ?_⟩
  intro i j hi hj
  exact hcl (e j) (e i) ((hkey j).2 hj) (fun h => by have := (hkey i).1 h; omega)

open DelayedBCN.Controllability in
theorem solution {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (Ct : Finset (Traj μ n)) :
    TrajControllableUnder F Ct ↔
      IsIrreducibleMat ((QDeleted F Ct).map (fun x : ℕ => (x : ℝ))) := by
  classical
  constructor
  · intro hC hR
    obtain ⟨e, r, hr1, hr2, hzero⟩ := hR
    have hN : 2 ≤ Fintype.card {a : Traj μ n // a ∉ Ct} := by omega
    let i0 : Fin (Fintype.card {a : Traj μ n // a ∉ Ct}) := ⟨0, by omega⟩
    let j0 : Fin (Fintype.card {a : Traj μ n // a ∉ Ct}) :=
      ⟨Fintype.card {a : Traj μ n // a ∉ Ct} - 1, by omega⟩
    obtain ⟨k, U, hU1, hU2⟩ := hC (e i0).1 (e j0).1 (e i0).2 (e j0).2
    have key : ∀ i, i ≤ k → ∀ h : trajAt F (e i0).1 U i ∉ Ct,
        (e.symm ⟨trajAt F (e i0).1 U i, h⟩).val < r := by
      intro i
      induction i with
      | zero =>
        intro _ h
        have : (⟨trajAt F (e i0).1 U 0, h⟩ : {x // x ∉ Ct}) = e i0 := Subtype.ext rfl
        rw [this, Equiv.symm_apply_apply]
        show 0 < r
        omega
      | succ i ih =>
        intro hi h
        have hik : i < k := by omega
        have hx : trajAt F (e i0).1 U i ∉ Ct := hU2 ⟨i, by omega⟩
        have hlt := ih (by omega) hx
        by_contra hge
        have hge' := Nat.le_of_not_lt hge
        have hz := hzero (e.symm ⟨trajAt F (e i0).1 U (i + 1), h⟩)
          (e.symm ⟨trajAt F (e i0).1 U i, hx⟩) hge' hlt
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hz
        exact f3ed_Q_pos F Ct ⟨trajAt F (e i0).1 U i, hx⟩ ⟨trajAt F (e i0).1 U (i + 1), h⟩
          (U ⟨i, hik⟩) (f3ed_trajAt_succ F (e i0).1 U i hik).symm hz
    have hk := key k le_rfl (hU2 ⟨k, by omega⟩)
    have : (⟨trajAt F (e i0).1 U k, hU2 ⟨k, by omega⟩⟩ : {x // x ∉ Ct}) = e j0 :=
      Subtype.ext hU1
    rw [this, Equiv.symm_apply_apply] at hk
    have : j0.val = Fintype.card {a : Traj μ n // a ∉ Ct} - 1 := rfl
    omega
  · intro hI
    by_contra hC
    apply hI
    unfold TrajControllableUnder at hC
    simp only [not_forall] at hC
    obtain ⟨a, b, ha, hb, hab⟩ := hC
    let p : {x : Traj μ n // x ∉ Ct} → Prop :=
      fun x => ∃ k : ℕ, ∃ U : Fin k → Input m, SteersAvoiding F a x.1 Ct U
    have hpa : p ⟨a, ha⟩ := by
      refine ⟨0, Fin.elim0, ?_, ?_⟩
      · rfl
      · intro i
        have : (i : ℕ) = 0 := by omega
        rw [this]
        exact ha
    have hpb : ¬ p ⟨b, hb⟩ := fun ⟨k, U, h⟩ => hab ⟨k, U, h⟩
    refine f3ed_reducible_of_closed _ p ⟨a, ha⟩ ⟨b, hb⟩ hpa hpb ?_
    intro x y hx hy
    by_contra hne
    obtain ⟨u, hu⟩ := f3ed_Q_ne F Ct x y hne
    exact hy (f3ed_extend F Ct a x.1 y.1 u y.2 hu hx)
