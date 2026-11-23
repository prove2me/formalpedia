-- Prove2me | solution 1 for Castro2006.H1_equiv_conjClasses
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T09:07:00.157869+00:00
-- url     : https://prove2.me/submissions/f7627ff7-bb61-4a6a-a5ed-4282926f2877

import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Definitions.Def_Castro2006_action
open CategoryTheory

namespace Castro2006GCH1

open groupCohomology

variable {G N : Type} [Group G] [CommGroup N] (φ : G →* MulAut N)

/-- `N` viewed in the representation. -/
def toA (n : N) : Castro2006.repOfMulAut φ := Additive.ofMul n
/-- The representation viewed as `N`. -/
def ofA (a : Castro2006.repOfMulAut φ) : N := Additive.toMul a

variable {φ}
theorem toA_mul (a b : N) : toA φ (a * b) = toA φ a + toA φ b := rfl
theorem toA_div (a b : N) : toA φ (a / b) = toA φ a - toA φ b := rfl
theorem ofA_add (a b : Castro2006.repOfMulAut φ) : ofA φ (a + b) = ofA φ a * ofA φ b := rfl
theorem ofA_zero : ofA φ 0 = 1 := rfl
theorem ofA_toA (n : N) : ofA φ (toA φ n) = n := rfl
theorem toA_ofA (a : Castro2006.repOfMulAut φ) : toA φ (ofA φ a) = a := rfl
theorem rho_toA (g : G) (n : N) : (Castro2006.repOfMulAut φ).ρ g (toA φ n) = toA φ (φ g n) := rfl
theorem rho_eq (g : G) (a : Castro2006.repOfMulAut φ) :
    (Castro2006.repOfMulAut φ).ρ g a = toA φ (φ g (ofA φ a)) := rfl
theorem toA_inj {a b : N} : toA φ a = toA φ b ↔ a = b := Iff.rfl
variable (φ)

theorem split_right (s : (SemidirectProduct.toGroupExtension φ).Splitting) (g : G) :
    (s g).right = g :=
  s.rightHom_splitting g

theorem conj_left (n : N) (x : N ⋊[φ] G) :
    (SemidirectProduct.inl n * x * (SemidirectProduct.inl n)⁻¹).left =
      n * x.left * φ x.right n⁻¹ := by
  simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left]

theorem conj_right (n : N) (x : N ⋊[φ] G) :
    (SemidirectProduct.inl n * x * (SemidirectProduct.inl n)⁻¹).right = x.right := by
  simp

/-- The 1-cocycle associated to a splitting. -/
noncomputable def cocycleOf (s : (SemidirectProduct.toGroupExtension φ).Splitting) :
    cocycles₁ (Castro2006.repOfMulAut φ) :=
  ⟨fun g => toA φ (s g).left, by
    rw [mem_cocycles₁_iff]
    intro g h
    rw [rho_toA, ← toA_mul, map_mul, SemidirectProduct.mul_left, split_right, mul_comm]⟩

/-- The splitting associated to a 1-cocycle. -/
noncomputable def splittingOf (f : cocycles₁ (Castro2006.repOfMulAut φ)) :
    (SemidirectProduct.toGroupExtension φ).Splitting where
  toFun g := ⟨ofA φ (f g), g⟩
  map_one' := by
    ext
    · change ofA φ (f 1) = 1
      rw [cocycles₁_map_one, ofA_zero]
    · rfl
  map_mul' g h := by
    have := (mem_cocycles₁_iff (f : G → _)).1 f.2 g h
    ext
    · change ofA φ (f (g * h)) = ofA φ (f g) * φ g (ofA φ (f h))
      rw [this, ofA_add, rho_eq, ofA_toA, mul_comm]
    · rfl
  rightInverse_rightHom g := rfl

theorem cocycleOf_splittingOf (f : cocycles₁ (Castro2006.repOfMulAut φ)) :
    cocycleOf φ (splittingOf φ f) = f := by
  ext g; rfl

theorem conj_iff (s s' : (SemidirectProduct.toGroupExtension φ).Splitting) :
    (SemidirectProduct.toGroupExtension φ).IsConj s s' ↔
      H1π _ (cocycleOf φ s) = H1π _ (cocycleOf φ s') := by
  rw [H1π_eq_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨toA φ n⁻¹, ?_⟩
    funext g
    have hl := congrArg SemidirectProduct.left (congrFun hn g)
    rw [SemidirectProduct.toGroupExtension_inl, conj_left, split_right] at hl
    change (Castro2006.repOfMulAut φ).ρ g (toA φ n⁻¹) - toA φ n⁻¹ =
      toA φ (s g).left - toA φ (s' g).left
    rw [rho_toA, ← toA_div, ← toA_div, toA_inj, hl, map_inv]
    rw [div_eq_div_iff_mul_eq_mul]
    simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel_left]
  · rintro ⟨x, hx⟩
    refine ⟨(ofA φ x)⁻¹, ?_⟩
    funext g
    have hg := congrFun hx g
    generalize ha : ofA φ x = a
    have hxa : x = toA φ a := by rw [← ha]; rfl
    rw [hxa] at hg
    change (Castro2006.repOfMulAut φ).ρ g (toA φ a) - toA φ a =
      toA φ (s g).left - toA φ (s' g).left at hg
    rw [rho_toA, ← toA_div, ← toA_div, toA_inj] at hg
    have hs : (s g).left = φ g a / a * (s' g).left := by rw [hg]; simp
    ext
    · rw [SemidirectProduct.toGroupExtension_inl, conj_left, split_right, inv_inv, hs,
        div_eq_mul_inv]
      ac_rfl
    · rw [SemidirectProduct.toGroupExtension_inl, conj_right, split_right, split_right]

end Castro2006GCH1

open Castro2006 in
theorem solution {G N : Type} [Group G] [CommGroup N] (φ : G →* MulAut N) :
    Nonempty ((SemidirectProduct.toGroupExtension φ).ConjClasses ≃
      groupCohomology (Castro2006.repOfMulAut φ) 1) := by
  refine ⟨Equiv.ofBijective
    (Quotient.lift (fun s => groupCohomology.H1π _ (Castro2006GCH1.cocycleOf φ s))
      (fun s s' h => (Castro2006GCH1.conj_iff φ s s').1 h)) ⟨?_, ?_⟩⟩
  · rintro ⟨s⟩ ⟨s'⟩ h
    exact Quotient.sound ((Castro2006GCH1.conj_iff φ s s').2 h)
  · intro x
    induction x using groupCohomology.H1_induction_on with
    | h f =>
      refine ⟨Quotient.mk _ (Castro2006GCH1.splittingOf φ f), ?_⟩
      change groupCohomology.H1π _ (Castro2006GCH1.cocycleOf φ _) = _
      rw [Castro2006GCH1.cocycleOf_splittingOf]
