-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f8dfcd51-a664-5020-9014-545a468eae03

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.GroupTheory.QuotientGroup.Basic
import Theorems.Thm_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem solution
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert G W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)
    (v₀ : W)
    (Φ : Additive (Abelianization G) →+ ↥(ribbonKernel D))
    (hΦ : ∀ g : G, (Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE e).1) v₀ g)
    (A : Type) [CommGroup A] (hdiv : ∀ (a : A) (n : ℕ), n ≠ 0 → ∃ b : A, b ^ n = a)
    (c : G →* A) (hc : ∀ (w : W) (g : G), g ∈ stabilizer G w → c g = 1) :
    ∃ ν : E → A, ∀ g : G, c g = ∏ e : E, ν e ^ ((Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) e) := by
  classical
  obtain ⟨hsurj, hker⟩ :=
    CerednikDrinfeld.Mumford.surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
      𝒯 hT τ hτ hadj D eE eV ha hb v₀ Φ hΦ

  let c' : Additive (Abelianization G) →+ Additive A := MonoidHom.toAdditive (Abelianization.lift c)
  have hc' : ∀ g : G, c' (Additive.ofMul (Abelianization.of g)) = Additive.ofMul (c g) := by
    intro g
    rfl

  have hkerle : Φ.ker ≤ c'.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    have hmem := (hker x).mp hx
    refine (AddSubgroup.closure_le (K := c'.ker) |>.mpr ?_) hmem
    rintro _ ⟨g, hg, rfl⟩
    rw [Set.mem_iUnion] at hg
    obtain ⟨w, hw⟩ := hg
    show c' (Additive.ofMul (Abelianization.of g)) = 0
    rw [hc', hc w g hw]
    rfl

  let e₀ := QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj
  let u₀ : ↥(ribbonKernel D) →+ Additive A :=
    (QuotientAddGroup.lift Φ.ker c' hkerle).comp e₀.symm.toAddMonoidHom
  have hu₀ : ∀ x : Additive (Abelianization G), u₀ (Φ x) = c' x := by
    intro x
    show (QuotientAddGroup.lift Φ.ker c' hkerle) (e₀.symm (Φ x)) = c' x
    have : e₀.symm (Φ x) = (QuotientAddGroup.mk x : Additive (Abelianization G) ⧸ Φ.ker) := by
      apply e₀.injective
      rw [AddEquiv.apply_symm_apply]
      rfl
    rw [this]
    rfl

  haveI : DivisibleBy (Additive A) ℤ :=
    { div := fun a n => if hn : n = 0 then 0 else
        Additive.ofMul ((Classical.choose (hdiv (Additive.toMul a) n.natAbs (Int.natAbs_ne_zero.mpr hn))) ^ (Int.sign n))
      div_zero := fun a => by simp
      div_cancel := by
        intro n a hn
        simp only [dif_neg hn]
        have hb := Classical.choose_spec (hdiv (Additive.toMul a) n.natAbs (Int.natAbs_ne_zero.mpr hn))
        have hs : n.sign * n = (n.natAbs : ℤ) := by
          rcases lt_or_gt_of_ne hn with h | h
          · rw [Int.sign_eq_neg_one_of_neg h]; omega
          · rw [Int.sign_eq_one_of_pos h]; omega
        apply Additive.toMul.injective
        rw [toMul_zsmul, toMul_ofMul, ← zpow_mul, hs, zpow_natCast, hb] }
  have hBaer : Module.Baer ℤ (Additive A) := Module.Baer.of_divisible _
  obtain ⟨u, hu⟩ := hBaer.extension_property (ribbonKernel D).subtype (ribbonKernel D).injective_subtype u₀.toIntLinearMap

  refine ⟨fun e => Additive.toMul (u (Pi.single e 1)), fun g => ?_⟩
  have h1 : Additive.ofMul (c g) = u ((Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ)) := by
    rw [← hc', ← hu₀]
    show _ = (u ∘ₗ (ribbonKernel D).subtype) (Φ (Additive.ofMul (Abelianization.of g)))
    rw [hu]
    rfl
  apply Additive.ofMul.injective
  rw [h1]
  set x : E → ℤ := (Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ)
  have hx : x = ∑ e, x e • Pi.single e (1 : ℤ) := by
    ext e'
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum, ofMul_prod]
  simp only [map_zsmul, ofMul_zpow, ofMul_toMul]

end S_CerednikDrinfeld_Mumford_exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq (solution)
