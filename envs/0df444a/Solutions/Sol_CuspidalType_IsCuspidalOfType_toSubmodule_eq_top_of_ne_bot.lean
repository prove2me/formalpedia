-- Prove2me | solution 1 for CuspidalType.IsCuspidalOfType.toSubmodule_eq_top_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1d1ea048-3700-540b-96ab-3b5aa3acee3e

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_IsCuspidalOfType_toSubmodule_eq_top_of_ne_bot

set_option autoImplicit false

open Polynomial

namespace CuStR1Engine

open CuspidalType

section B2

variable {q : ℕ} [Fact q.Prime] {F : Type*} [Field F]

private def translate (s : ZMod q) (f : ZMod q → F) : ZMod q → F := fun x => f (x + s)

private def scale (a : (ZMod q)ˣ) (f : ZMod q → F) : ZMod q → F := fun x => f ((a : ZMod q) * x)

private def sumZero (q : ℕ) [Fact q.Prime] (F : Type*) [Field F] : Submodule F (ZMod q → F) :=
  LinearMap.ker (∑ x : ZMod q, LinearMap.proj x)

private theorem mem_sumZero {f : ZMod q → F} : f ∈ sumZero q F ↔ ∑ x, f x = 0 := by
  simp [sumZero, LinearMap.mem_ker, LinearMap.sum_apply]

private def qDeltaSubOne (F : Type*) [Field F] (x : ZMod q) : ZMod q → F := fun y => (if y = x then (q : F) else 0) - 1

private theorem translate_qDeltaSubOne (s x : ZMod q) :
    translate s (qDeltaSubOne F x) = qDeltaSubOne F (x - s) := by
  funext y
  simp only [translate, qDeltaSubOne]
  congr 1
  simp [eq_sub_iff_add_eq]

private theorem sumZero_le_span_qDeltaSubOne (hq : (q : F) ≠ 0) :
    sumZero q F ≤ Submodule.span F (Set.range (qDeltaSubOne (q := q) F)) := by
  intro f hf
  rw [mem_sumZero] at hf
  have key : f = (q : F)⁻¹ • ∑ x, f x • qDeltaSubOne F x := by
    funext y
    simp only [qDeltaSubOne, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_sub, mul_ite, mul_zero, mul_one,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, hf, sub_zero]
    field_simp
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun x _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩))

private theorem sum_scale_eq (f : ZMod q → F) (hf : ∑ x, f x = 0) :
    ∑ a : (ZMod q)ˣ, scale a f = f 0 • qDeltaSubOne F 0 := by
  funext y
  simp only [Finset.sum_apply, scale, Pi.smul_apply, qDeltaSubOne, smul_eq_mul]
  by_cases hy : y = 0
  · subst hy
    simp only [mul_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, if_true]
    rw [ZMod.card_units q, Nat.cast_sub (Fact.out : q.Prime).one_le, Nat.cast_one]
    ring
  · rw [if_neg hy, zero_sub, mul_neg_one]
    have h1 : ∑ a : (ZMod q)ˣ, f ((a : ZMod q) * y) = ∑ b : (ZMod q)ˣ, f (b : ZMod q) := by
      refine (Fintype.sum_equiv (Equiv.mulRight (Units.mk0 y hy)) _ _ fun a => ?_)
      simp
    have h2 : ∑ b : (ZMod q)ˣ, f (b : ZMod q) = ∑ z ∈ (Finset.univ.erase (0 : ZMod q)), f z := by
      rw [Finset.sum_subtype (Finset.univ.erase (0 : ZMod q)) (p := fun z : ZMod q => z ≠ 0) (fun z => by simp)]
      exact Fintype.sum_equiv unitsEquivNeZero _ _ fun b => rfl
    rw [h1, h2, Finset.sum_erase_eq_sub (Finset.mem_univ _), hf, zero_sub]

private theorem eq_sumZero_of_stable (hq : (q : F) ≠ 0) (N : Submodule F (ZMod q → F)) (hN : N ≤ sumZero q F)
    (htr : ∀ s f, f ∈ N → translate s f ∈ N) (hsc : ∀ a f, f ∈ N → scale a f ∈ N) (hne : N ≠ ⊥) :
    N = sumZero q F := by
  refine le_antisymm hN ?_
  obtain ⟨f, hfN, hf0⟩ := (Submodule.ne_bot_iff N).mp hne
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (funext h)
  set g := translate x₀ f with hg
  have hgN : g ∈ N := htr x₀ f hfN
  have hg0 : g 0 ≠ 0 := by simpa [hg, translate] using hx₀
  have hgsum : ∑ x, g x = 0 := mem_sumZero.mp (hN hgN)
  have havg : g 0 • qDeltaSubOne F (0 : ZMod q) ∈ N := by
    rw [← sum_scale_eq g hgsum]
    exact Submodule.sum_mem _ fun a _ => hsc a g hgN
  have h0 : qDeltaSubOne F (0 : ZMod q) ∈ N := by
    have := N.smul_mem (g 0)⁻¹ havg
    rwa [smul_smul, inv_mul_cancel₀ hg0, one_smul] at this
  have hall : ∀ x : ZMod q, qDeltaSubOne F x ∈ N := fun x => by
    have := htr (-x) _ h0
    rwa [translate_qDeltaSubOne, zero_sub, neg_neg] at this
  refine (sumZero_le_span_qDeltaSubOne hq).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨x, rfl⟩
  exact hall x

private theorem finrank_sumZero (q : ℕ) [Fact q.Prime] (F : Type*) [Field F] : Module.finrank F
    (sumZero q F) = q - 1 := by
  classical
  have hsurj : LinearMap.range (∑ x : ZMod q, (LinearMap.proj x : (ZMod q → F) →ₗ[F] F)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨Pi.single 0 c, by simp [LinearMap.sum_apply, Pi.single_apply]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (∑ x : ZMod q, (LinearMap.proj x : (ZMod q → F) →ₗ[F] F))
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card, ZMod.card] at h
  unfold sumZero
  omega

end B2

section Core

variable (q : ℕ) [Fact q.Prime]

private theorem unipotent_add (s t : ZMod q) : unipotent q (s + t) = unipotent q s * unipotent q t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem unipotent_zero : unipotent q 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

private theorem diagElem_mul (a b : (ZMod q)ˣ) : diagElem q (a * b) = diagElem q a * diagElem q b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagElem_one : diagElem q 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

private theorem diagElem_mul_unipotent (a : (ZMod q)ˣ) (t : ZMod q) :
    diagElem q a * unipotent q t = unipotent q ((a : ZMod q) * t) * diagElem q a := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {q} {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (ρ : Representation F (GL2 q) V)

omit [FiniteDimensional F V] in
private theorem trace_diagElem_eq_zero (hsum : ∑ t : ZMod q, ρ (unipotent q t) = 0) (hq : (q : F) ≠ 0) (a : (ZMod q)ˣ)
    (ha : a ≠ 1) : LinearMap.trace F V (ρ (diagElem q a)) = 0 := by

  have hconj : ∀ t : ZMod q, LinearMap.trace F V (ρ (diagElem q a) * ρ (unipotent q t)) =
      LinearMap.trace F V (ρ (diagElem q a)) := by
    intro t

    have hunit : ((a : ZMod q)⁻¹ - 1) ≠ 0 := fun h =>
      ha (Units.val_eq_one.mp (inv_eq_one.mp (sub_eq_zero.mp h)))
    set s : ZMod q := t / ((a : ZMod q)⁻¹ - 1) with hs
    have ht : t = ((a : ZMod q)⁻¹ - 1) * s := by rw [hs, mul_div_cancel₀ _ hunit]
    have hab : (a : ZMod q) * (a : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ a.ne_zero
    have hkey : unipotent q s * diagElem q a * unipotent q (-s) = diagElem q a * unipotent q t := by
      rw [ht]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, -ZMod.inv_coe_unit]
      linear_combination (-s) * hab
    rw [← ρ.map_mul, ← hkey, ρ.map_mul, LinearMap.trace_mul_comm, ← ρ.map_mul, ← mul_assoc, ← unipotent_add,
      neg_add_cancel, unipotent_zero, one_mul]
  have h0 : ∑ t : ZMod q, LinearMap.trace F V (ρ (diagElem q a) * ρ (unipotent q t)) = 0 := by
    rw [← map_sum, ← Finset.mul_sum, hsum, mul_zero, map_zero]
  simp only [hconj, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at h0
  exact (mul_eq_zero.mp h0).resolve_left hq

private theorem exists_diag_fixed (hsum : ∑ t : ZMod q, ρ (unipotent q t) = 0) (hq : (q : F) ≠ 0)
    (hq1 : ((q : F) - 1) ≠ 0) (hdim : Module.finrank F V = q - 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ a : (ZMod q)ˣ, ρ (diagElem q a) v = v := by
  set e : Module.End F V := ∑ a : (ZMod q)ˣ, ρ (diagElem q a) with he
  have htr : LinearMap.trace F V e = (q : F) - 1 := by
    rw [he, map_sum, Finset.sum_eq_single (1 : (ZMod q)ˣ)]
    · rw [diagElem_one, map_one, LinearMap.trace_one, hdim, Nat.cast_sub (Fact.out : q.Prime).one_le, Nat.cast_one]
    · intro a _ ha; exact trace_diagElem_eq_zero ρ hsum hq a ha
    · intro h; exact absurd (Finset.mem_univ _) h
  have hne : e ≠ 0 := fun h => hq1 (by rw [← htr, h, map_zero])
  obtain ⟨w, hw⟩ : ∃ w, e w ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  refine ⟨e w, hw, fun b => ?_⟩
  have hb : ρ (diagElem q b) * e = e := by
    rw [he, Finset.mul_sum]
    simp_rw [← ρ.map_mul, ← diagElem_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft b) _ _ fun a => rfl
  calc ρ (diagElem q b) (e w) = (ρ (diagElem q b) * e) w := rfl
    _ = e w := by rw [hb]

end Core

section Assemble

variable {q : ℕ} [Fact q.Prime] {F : Type*} [Field F]

private theorem qDeltaSubOne_mem (x : ZMod q) : qDeltaSubOne F x ∈ sumZero q F := by
  rw [mem_sumZero]
  simp [qDeltaSubOne, Finset.sum_sub_distrib, Finset.card_univ, ZMod.card]

private theorem sum_translate (s : ZMod q) (f : ZMod q → F) : ∑ x, translate s f x = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.addRight s) _ _ fun _ => rfl

private theorem sum_scale (a : (ZMod q)ˣ) (f : ZMod q → F) : ∑ x, scale a f x = ∑ x, f x :=
  Fintype.sum_equiv (Units.mulLeft a) _ _ fun _ => rfl

private theorem translate_mem_sumZero (s : ZMod q) {f : ZMod q → F} (hf : f ∈ sumZero q F)
    : translate s f ∈ sumZero q F := by
  rw [mem_sumZero] at hf ⊢
  rw [sum_translate, hf]

private theorem scale_mem_sumZero (a : (ZMod q)ˣ) {f : ZMod q → F} (hf : f ∈ sumZero q F)
    : scale a f ∈ sumZero q F := by
  rw [mem_sumZero] at hf ⊢
  rw [sum_scale, hf]

variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F (GL2 q) V)

private noncomputable def orbitMap (v₀ : V) : (ZMod q → F) →ₗ[F] V :=
  ∑ x : ZMod q, (LinearMap.proj x : (ZMod q → F) →ₗ[F] F).smulRight (ρ (unipotent q x) v₀)

private theorem orbitMap_apply (v₀ : V) (f : ZMod q → F) : orbitMap ρ v₀ f = ∑ x, f x • ρ (unipotent q x) v₀ := by
  simp [orbitMap, LinearMap.sum_apply]

private theorem orbitMap_translate (v₀ : V) (s : ZMod q) (f : ZMod q → F) :
    orbitMap ρ v₀ (translate s f) = ρ (unipotent q (-s)) (orbitMap ρ v₀ f) := by
  rw [orbitMap_apply, orbitMap_apply, map_sum]
  simp only [map_smul]
  refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun x => ?_
  simp only [translate, Equiv.coe_addRight]
  rw [← Module.End.mul_apply, ← map_mul, ← unipotent_add, add_comm x s, neg_add_cancel_left]

private theorem orbitMap_scale (v₀ : V) (hv₀ : ∀ a : (ZMod q)ˣ, ρ (diagElem q a) v₀ = v₀) (a : (ZMod q)ˣ)
    (f : ZMod q → F) :
    orbitMap ρ v₀ (scale a f) = ρ (diagElem q a⁻¹) (orbitMap ρ v₀ f) := by
  rw [orbitMap_apply, orbitMap_apply, map_sum]
  simp only [map_smul]
  refine Fintype.sum_equiv (Units.mulLeft a) _ _ fun x => ?_
  simp only [scale, Units.mulLeft_apply]
  rw [← Module.End.mul_apply, ← map_mul, diagElem_mul_unipotent, map_mul, Module.End.mul_apply, hv₀,
    Units.inv_mul_cancel_left]

private theorem orbitMap_qDeltaSubOne_zero (v₀ : V) (hsum : ∑ t : ZMod q, ρ (unipotent q t) = 0) :
    orbitMap ρ v₀ (qDeltaSubOne F 0) = (q : F) • v₀ := by
  rw [orbitMap_apply]
  simp only [qDeltaSubOne, sub_smul, ite_smul, zero_smul, one_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, unipotent_zero, map_one, Module.End.one_apply]
  rw [← LinearMap.sum_apply, hsum, LinearMap.zero_apply, sub_zero]

private theorem isIrreducible_of_sum_unipotent_eq_zero [FiniteDimensional F V]
    (hsum : ∑ t : ZMod q, ρ (unipotent q t) = 0)
    (hq : (q : F) ≠ 0) (hq1 : ((q : F) - 1) ≠ 0) (hdim : Module.finrank F V = q - 1) : ρ.IsIrreducible := by
  obtain ⟨v₀, hv₀, hfix⟩ := exists_diag_fixed ρ hsum hq hq1 hdim
  set φ := orbitMap ρ v₀ with hφ

  have stable : ∀ N : Submodule F V, (∀ g : GL2 q, ∀ v ∈ N, ρ g v ∈ N) →
      (N.comap φ ⊓ sumZero q F = ⊥ ∨ N.comap φ ⊓ sumZero q F = sumZero q F) := by
    intro N hN
    by_cases hbot : N.comap φ ⊓ sumZero q F = ⊥
    · exact Or.inl hbot
    · right
      refine eq_sumZero_of_stable hq _ inf_le_right ?_ ?_ hbot
      · rintro s f ⟨hf, hf'⟩
        exact ⟨by simpa [Submodule.mem_comap, hφ, orbitMap_translate] using hN _ _ hf, translate_mem_sumZero s hf'⟩
      · rintro a f ⟨hf, hf'⟩
        exact ⟨by simpa [Submodule.mem_comap, hφ, orbitMap_scale ρ v₀ hfix] using hN _ _ hf, scale_mem_sumZero a hf'⟩

  have hker : (⊥ : Submodule F V).comap φ ⊓ sumZero q F = ⊥ := by
    refine (stable ⊥ fun g v hv => by simp_all).resolve_right fun heq => ?_
    have hmem : qDeltaSubOne F (0 : ZMod q) ∈ (⊥ : Submodule F V).comap φ ⊓ sumZero q F := by
      rw [heq]; exact qDeltaSubOne_mem 0
    have h0 : φ (qDeltaSubOne F 0) = 0 := by simpa using hmem.1
    rw [hφ, orbitMap_qDeltaSubOne_zero ρ v₀ hsum] at h0
    exact smul_ne_zero hq hv₀ h0
  have hinj : Function.Injective (φ.domRestrict (sumZero q F)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨f, hf⟩ hf0
    have : f ∈ (⊥ : Submodule F V).comap φ ⊓ sumZero q F := ⟨by simpa using hf0, hf⟩
    rw [hker] at this
    exact Subtype.ext (by simpa using this)

  have hrange : LinearMap.range (φ.domRestrict (sumZero q F)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hinj, finrank_sumZero, hdim]
  have hnt : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := F) (by rw [hdim]; exact Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt)

  haveI : Nontrivial (Subrepresentation ρ) :=
    ⟨⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
  refine ⟨fun N => ?_⟩
  rcases stable N.toSubmodule (fun g v hv => N.apply_mem_toSubmodule g hv) with hN | hN
  · left
    apply Subrepresentation.toSubmodule_injective
    refine (Submodule.eq_bot_iff _).mpr fun n hn => ?_
    obtain ⟨⟨f, hf⟩, rfl⟩ := (LinearMap.range_eq_top.mp hrange) n
    have : f ∈ N.toSubmodule.comap φ ⊓ sumZero q F := ⟨by simpa using hn, hf⟩
    rw [hN] at this
    simp [(Submodule.mem_bot F).mp this]
  · right
    apply Subrepresentation.toSubmodule_injective
    refine top_unique fun n _ => ?_
    obtain ⟨⟨f, hf⟩, rfl⟩ := (LinearMap.range_eq_top.mp hrange) n
    have hfN : f ∈ N.toSubmodule.comap φ ⊓ sumZero q F := by rw [hN]; exact hf
    simpa using hfN.1

end Assemble

section Bridge

variable {q : ℕ} [Fact q.Prime] {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
  (ρ : Representation F (GL2 q) V)

private theorem sum_unipotent_eq_zero_of_cuspidal (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) :
    ∑ t : ZMod q, ρ (unipotent q t) = 0 := by
  ext v
  rw [LinearMap.sum_apply, LinearMap.zero_apply]
  apply hcusp
  intro s
  rw [map_sum]
  simp_rw [← Module.End.mul_apply, ← ρ.map_mul, ← unipotent_add]
  exact Fintype.sum_equiv (Equiv.addLeft s) _ _ fun _ => rfl

end Bridge

end CuStR1Engine

open Polynomial CuspidalType

open CuStR1Engine in

theorem solution {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V} (h : IsCuspidalOfType θ ρ)
    (hq : (q : K) ≠ 0) (hq1 : ((q : K) - 1 ≠ 0)) (W : Subrepresentation ρ) (hW : W.toSubmodule ≠ ⊥) :
    W.toSubmodule = ⊤ := by
  haveI hirr : ρ.IsIrreducible :=
    isIrreducible_of_sum_unipotent_eq_zero ρ (sum_unipotent_eq_zero_of_cuspidal ρ h.cuspidal) hq hq1 h.finrank_eq
  rcases IsSimpleOrder.eq_bot_or_eq_top W with hbot | htop
  · exact absurd (congrArg Subrepresentation.toSubmodule hbot) hW
  · exact congrArg Subrepresentation.toSubmodule htop

end S_CuspidalType_IsCuspidalOfType_toSubmodule_eq_top_of_ne_bot
end P2MW
export P2MW.S_CuspidalType_IsCuspidalOfType_toSubmodule_eq_top_of_ne_bot (solution)
