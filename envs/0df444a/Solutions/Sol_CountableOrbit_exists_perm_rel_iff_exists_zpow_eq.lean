-- Prove2me | solution 1 for CountableOrbit.exists_perm_rel_iff_exists_zpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T19:34:53.911093+00:00
-- url     : https://prove2.me/submissions/11aea284-e71a-455a-9829-d16798bc84af

import Mathlib

section
namespace CountableOrbit

theorem addRight_one_zpow_apply (n : ℤ) (z : ℤ) : ((Equiv.addRight (1 : ℤ)) ^ n) z = z + n := by
  induction n using Int.induction_on generalizing z with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih]
    simp only [Equiv.coe_addRight]
    ring
  | pred n ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    simp only [Equiv.Perm.inv_def, Equiv.addRight_symm, Equiv.coe_addRight]
    ring

theorem permCongr_zpow {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α) (n : ℤ) :
    e.permCongr p ^ n = e.permCongr (p ^ n) := by
  have h1 := map_zpow e.permCongrHom p n
  simp only [Equiv.permCongrHom, MulEquiv.coe_mk] at h1
  exact h1.symm

/-- A countable type carries a permutation with a single orbit. -/
theorem exists_perm_forall_exists_zpow_eq (α : Type*) [Countable α] :
    ∃ σ : Equiv.Perm α, ∀ a b : α, ∃ n : ℤ, (σ ^ n) a = b := by
  rcases finite_or_infinite α with hfin | hinf
  · obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin α
    refine ⟨e.symm.permCongr (finRotate k), fun a b => ?_⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (finRotate k ^ n) (e a) = e b := by
      match k, e with
      | 0, e => exact (e a).elim0
      | 1, e => exact ⟨0, Subsingleton.elim _ _⟩
      | m + 2, e =>
        have hmove : ∀ i : Fin (m + 2), finRotate (m + 2) i ≠ i := by
          intro i h
          rw [finRotate_apply] at h
          simp at h
        exact isCycle_finRotate.exists_zpow_eq (hmove _) (hmove _)
    refine ⟨n, ?_⟩
    rw [permCongr_zpow, Equiv.permCongr_apply]
    simp [hn]
  · have : Encodable α := Encodable.ofCountable α
    have : Denumerable α := Denumerable.ofEncodableOfInfinite α
    let e : α ≃ ℤ := (Denumerable.eqv α).trans Equiv.intEquivNat.symm
    refine ⟨e.symm.permCongr (Equiv.addRight 1), fun a b => ⟨e b - e a, ?_⟩⟩
    rw [permCongr_zpow, Equiv.permCongr_apply, Equiv.symm_symm, addRight_one_zpow_apply]
    simp

/-- Every equivalence relation with countable classes is the orbit relation of a single
permutation (no measurability asked of it). -/
theorem exists_perm_rel_iff_exists_zpow_eq {X : Type*} (r : X → X → Prop) (hr : Equivalence r)
    (hc : ∀ x, {y | r x y}.Countable) :
    ∃ T : Equiv.Perm X, ∀ x y, r x y ↔ ∃ n : ℤ, (T ^ n) x = y := by
  let s : Setoid X := ⟨r, hr⟩
  let f : X → Quotient s := Quotient.mk s
  have hcount : ∀ q : Quotient s, Countable {x // f x = q} := by
    intro q
    obtain ⟨x0, rfl⟩ := Quotient.exists_rep q
    have := (hc x0).to_subtype
    let g : {x // f x = f x0} → {y | r x0 y} :=
      fun x => ⟨x.1, hr.symm (Quotient.exact x.2)⟩
    exact Function.Injective.countable (f := g)
      (fun a b h => Subtype.ext (congrArg (fun z : {y | r x0 y} => (z : X)) h))
  choose σ hσ using fun q => @exists_perm_forall_exists_zpow_eq {x // f x = q} (hcount q)
  let e := Equiv.sigmaFiberEquiv f
  have hpow : ∀ n : ℤ, (e.permCongr (Equiv.Perm.sigmaCongrRight σ)) ^ n =
      e.permCongr (Equiv.Perm.sigmaCongrRight (σ ^ n)) := by
    intro n
    have h1 := map_zpow e.permCongrHom (Equiv.Perm.sigmaCongrRight σ) n
    have h2 := map_zpow (Equiv.Perm.sigmaCongrRightHom (fun q => {x // f x = q})) σ n
    simp only [Equiv.permCongrHom, MulEquiv.coe_mk] at h1
    rw [← h1]
    congr 1
    exact h2.symm
  have happ : ∀ (n : ℤ) (x : X),
      ((e.permCongr (Equiv.Perm.sigmaCongrRight σ)) ^ n) x = (((σ (f x)) ^ n) ⟨x, rfl⟩).1 := by
    intro n x
    rw [hpow]
    rfl
  refine ⟨e.permCongr (Equiv.Perm.sigmaCongrRight σ), fun x y => ⟨fun hxy => ?_, ?_⟩⟩
  · have hq : f y = f x := Quotient.sound (hr.symm hxy)
    obtain ⟨n, hn⟩ := hσ (f x) ⟨x, rfl⟩ ⟨y, hq⟩
    exact ⟨n, by rw [happ, hn]⟩
  · rintro ⟨n, rfl⟩
    rw [happ]
    exact hr.symm (Quotient.exact ((((σ (f x)) ^ n) ⟨x, rfl⟩).2))

end CountableOrbit
end



open CountableOrbit in
theorem solution {X : Type*} (r : X → X → Prop) (hr : Equivalence r)
    (hc : ∀ x, {y | r x y}.Countable) :
    ∃ T : Equiv.Perm X, ∀ x y, r x y ↔ ∃ n : ℤ, (T ^ n) x = y :=
  by
  try haveI := r; try haveI := hr; try haveI := hc; first
    | exact CountableOrbit.exists_perm_rel_iff_exists_zpow_eq r hr hc
    | exact CountableOrbit.exists_perm_rel_iff_exists_zpow_eq
    | exact CountableOrbit.exists_perm_rel_iff_exists_zpow_eq ..
    | (apply CountableOrbit.exists_perm_rel_iff_exists_zpow_eq <;> first | assumption | infer_instance)
    | simpa using CountableOrbit.exists_perm_rel_iff_exists_zpow_eq
