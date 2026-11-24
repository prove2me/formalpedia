-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.t1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:59.000266+00:00
-- url     : https://prove2.me/submissions/fc317f46-2ebc-48f1-a440-b901bdc7e3c6

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_primeToPart_pow
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_primeToPart_coprime
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_primeToPart_isOfFinOrder
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_ne_zero_of_mem
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_exists_index
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_isOfFinOrder_of_index
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_exists_dvd
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_mem_cycleType_of_factor
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_isOrbit_of_mem
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_sum_blocks
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_stable_of_subSum
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL_apply
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL_injective
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_charpoly_repGL
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_glEquiv_apply
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_irred
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (hR : Restriction) : IrreducibilityCriterion := by
  intro N g hgf PP J f χ _hBB hgood ℓ hℓf i hℓ G hGg ρ τ φ ι hconj hinj hchar
  classical
  have hℓp : ℓ.Prime := hℓf.out
  have hℓg : ℓ ≠ g i := fun h => hℓ (by rw [h]; exact Set.mem_union_left _ (Set.mem_singleton _))
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG6⟩ := hgood i
  have hpoly : ∀ v, GoodPoly N (f i v) := fun v => ⟨(hG1 v).1, (hG1 v).2.1, (hG1 v).2.2, hG2 v⟩
  choose r σ hr hrf hσ using fun v => exists_index (hpoly v)
  have hmemr : ∀ v j, r v j ∈ rootsBar (f i v) := by
    intro v j; rw [← hrf v]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
  have hr0 : ∀ v j, r v j ≠ 0 := fun v j => ne_zero_of_mem (hpoly v) (hmemr v j)
  have hrfin : ∀ v j, IsOfFinOrder (r v j) := fun v j => isOfFinOrder_of_index (hσ v) j (hr0 v j)
  set L : PP i → Fin N → Fbar ℓ := fun v j => ι v (primeToPart ℓ (r v j)) with hLdef
  have hptp0 : ∀ v j, primeToPart ℓ (r v j) ≠ 0 := by
    intro v j; unfold primeToPart; exact pow_ne_zero _ (hr0 v j)
  have hptpc : ∀ v j, (orderOf (primeToPart ℓ (r v j))).Coprime ℓ :=
    fun v j => primeToPart_coprime hℓp _ (hrfin v j)
  have hLinj : ∀ v, Function.Injective (L v) := by
    intro v j k h
    have h1 := hinj v _ _ (hptp0 v j) (hptp0 v k) (hptpc v j) (hptpc v k) h
    exact hr v (hG3 ℓ hℓp hℓ v _ (hmemr v j) _ (hmemr v k) h1)
  have hLσ : ∀ v j, L v (σ v j) = L v j ^ (g i) := by
    intro v j
    show ι v (primeToPart ℓ (r v (σ v j))) = ι v (primeToPart ℓ (r v j)) ^ (g i)
    rw [hσ v j, primeToPart_pow, map_pow]
    exact orderOf_injective (frobenius (Fbar (g i)) (g i)).toMonoidHom (frobenius_inj _ _) (r v j)
  have hroots : ∀ v, (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly.roots =
      Finset.univ.val.map (L v) := by
    intro v
    have hcp : (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly =
        ((Finset.univ.val.map (L v)).map fun a => X - C a).prod := by
      rw [hchar v, ← hrf v, Multiset.map_map, Multiset.map_map]; rfl
    rw [hcp, roots_multiset_prod_X_sub_C]

  have hirr : IrredOn ρ ⊤ := by
    intro W hW
    refine Formalism.GaloisIrreducibility.irred (Fbar ℓ) (Fin N → Fbar ℓ) (PP i) (Finset (Fbar ℓ))
      (fun v => repGL (ρ (τ v))) (fun v => glEquiv (ρ (φ v))) (fun _ => g i)
      (fun _ S => S) (fun v => blocks (σ v) (L v)) ?_ ?_ ?_ ?_ W ?_ ?_
    · intro v x
      show repGL (ρ (φ v)) (repGL (ρ (τ v)) x) = (repGL (ρ (τ v)) ^ g i) (repGL (ρ (φ v)) x)
      have heq : ρ (φ v) * ρ (τ v) = ρ (τ v) ^ g i * ρ (φ v) := by
        have h := hconj v
        rw [map_mul, map_mul, map_inv] at h
        rw [← h, inv_mul_cancel_right]
      rw [← map_pow, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul repGL, ← map_mul repGL, heq]
    · intro v S hS; exact isOrbit_of_mem (hLσ v) hS
    · intro v
      show (LinearMap.charpoly (repGL (ρ (τ v)))).roots = _
      rw [charpoly_repGL, hroots v, sum_blocks (hLinj v)]
    · intro a ha h2a
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2a
      obtain ⟨v, hv⟩ := hG5 a ha h2a
      refine ⟨v, fun hs => hv ?_⟩
      obtain ⟨A, hA, hAc⟩ := stable_of_subSum (hLinj v) hs
      obtain ⟨Q, -, hQf, hQd, -⟩ := exists_dvd (hpoly v) (hrf v) (hσ v) A hA
      exact ⟨Q, hQf, hQd.trans hAc⟩
    · intro v x hx
      show repGL (ρ (τ v)) x ∈ W
      rw [repGL_apply]; exact hW _ (Subgroup.mem_top _) x hx
    · intro v x hx
      show glEquiv (ρ (φ v)) x ∈ W
      rw [glEquiv_apply, repGL_apply]; exact hW _ (Subgroup.mem_top _) x hx

  have hpart3 : ∀ v j, ¬ (Matrix.charpoly (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ))).IsRoot
      (ι v (primeToPart ℓ (algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i))))) := by
    intro v j hroot
    have hmem := (mem_roots (Matrix.charpoly_monic _).ne_zero).mpr hroot
    rw [hroots v] at hmem
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp hmem
    have hc0 : algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i)) ≠ 0 :=
      (_root_.map_ne_zero _).mpr (χ i v j).ne_zero
    have hcfin : IsOfFinOrder (algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i))) :=
      MonoidHom.isOfFinOrder ((algebraMap (ZMod (g i)) (Fbar (g i))).toMonoidHom.comp (Units.coeHom _))
        (isOfFinOrder_of_finite (χ i v j))
    have h1 := hinj v _ _ (hptp0 v k) (by unfold primeToPart; exact pow_ne_zero _ hc0)
      (hptpc v k) (primeToPart_coprime hℓp _ hcfin) hk
    exact hG4 ℓ hℓp hℓg v j _ (hmemr v k) h1

  have hpart2 : ∀ (H : Subgroup G) [H.Normal], Finite (G ⧸ H) → Group.IsSolvable (G ⧸ H) →
      (∀ v, τ v ∈ H) → IrredOn ρ H := by
    intro H hHn hfin hsolv hτH W hW
    obtain ⟨v₀, q₀, hq₀i, hq₀f, hq₀p, hN2, hN3⟩ := hG6
    have hpc : q₀.natDegree ∈ (σ v₀).cycleType :=
      mem_cycleType_of_factor (hpoly v₀) (hr v₀) (hrf v₀) (hσ v₀) q₀ hq₀i hq₀f hq₀p
    have hN8 : 8 ≤ N := by
      have h2 := hq₀p.two_le
      have h5 : 5 ≤ q₀.natDegree := by
        rcases (show q₀.natDegree = 2 ∨ q₀.natDegree = 3 ∨ q₀.natDegree = 4 ∨
          5 ≤ q₀.natDegree by omega) with h | h | h | h
        · omega
        · omega
        · exact absurd (h ▸ hq₀p) (by norm_num)
        · exact h
      omega
    let ρΓ : Representation (Fbar ℓ) ρ.range (Fin N → Fbar ℓ) := repGL.comp ρ.range.subtype
    have hρΓ : ∀ (y : ρ.range) x, ρΓ y x = repGL (y : GL (Fin N) (Fbar ℓ)) x := fun _ _ => rfl
    have hinjΓ : Function.Injective ρΓ := fun a b h => Subtype.ext (repGL_injective h)
    let H' : Subgroup ρ.range := H.map ρ.rangeRestrict
    have hH' : H'.Normal := hHn.map _ ρ.rangeRestrict_surjective
    have hle : H ≤ H'.comap ρ.rangeRestrict := fun h hh => Subgroup.mem_map_of_mem _ hh
    let ψ := QuotientGroup.map H H' ρ.rangeRestrict hle
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨x, rfl⟩ := ρ.rangeRestrict_surjective z
      exact ⟨QuotientGroup.mk x, rfl⟩
    have hfin' : Finite (ρ.range ⧸ H') := Finite.of_surjective ψ hψ
    have hsolv' : Group.IsSolvable (ρ.range ⧸ H') := Group.isSolvable_of_surjective hψ
    let T : ρ.range := ρ.rangeRestrict (τ v₀)
    let Φ : ρ.range := ρ.rangeRestrict (φ v₀)
    have hTΦ : Φ * T * Φ⁻¹ = T ^ (g i) := by
      show ρ.rangeRestrict (φ v₀) * ρ.rangeRestrict (τ v₀) * (ρ.rangeRestrict (φ v₀))⁻¹ =
        ρ.rangeRestrict (τ v₀) ^ (g i)
      rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
      apply Subtype.ext
      rw [MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, hconj v₀, map_pow]

    have hev : ∀ j, (repGL (ρ (τ v₀))).HasEigenvalue (L v₀ j) := by
      intro j
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, charpoly_repGL]
      have : L v₀ j ∈ (ρ (τ v₀) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly.roots := by
        rw [hroots v₀]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
      exact (mem_roots (Matrix.charpoly_monic _).ne_zero).mp this
    choose w hw using fun j => (hev j).exists_hasEigenvector
    have hli : LinearIndependent (Fbar ℓ) w :=
      Module.End.eigenvectors_linearIndependent' _ (L v₀) (hLinj v₀) w hw
    let e : Module.Basis (Fin N) (Fbar ℓ) (Fin N → Fbar ℓ) :=
      basisOfLinearIndependentOfCardEqFinrank' w hli (by rw [Module.finrank_fintype_fun_eq_card])
    have he : ∀ j, e j = w j := fun j => by simp [e]
    have hTpow : ∀ (n : ℕ) j, ρΓ (T ^ n) (e j) = L v₀ j ^ n • e j := by
      intro n j
      rw [map_pow, he]
      exact (hw j).pow_apply n
    have hlfin : ∀ j, IsOfFinOrder (L v₀ j) :=
      fun j => (ι v₀).isOfFinOrder (primeToPart_isOfFinOrder ℓ _ (hrfin v₀ j))
    have hMo : 0 < ∏ j, orderOf (L v₀ j) := Finset.prod_pos (fun j _ => (hlfin j).orderOf_pos)
    have hlM : ∀ j, L v₀ j ^ (∏ j, orderOf (L v₀ j)) = 1 := fun j =>
      orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
    have hTfin : IsOfFinOrder T := by
      rw [isOfFinOrder_iff_pow_eq_one]
      refine ⟨_, hMo, hinjΓ ?_⟩
      rw [map_one]
      exact e.ext (fun j => by rw [hTpow, hlM, one_smul]; rfl)
    let I : Subgroup ρ.range := Subgroup.zpowers T
    have hInat : ∀ y ∈ I, ∃ n : ℕ, T ^ n = y := fun y hy =>
      (Submonoid.mem_powers_iff _ _).mp (hTfin.mem_powers_iff_mem_zpowers.mpr hy)
    have hconjI : ∀ y ∈ I, Φ * y * Φ⁻¹ ∈ I := by
      intro y hy
      obtain ⟨n, rfl⟩ := hInat y hy
      rw [← conj_pow, hTΦ, ← pow_mul]
      exact Subgroup.npow_mem_zpowers _ _
    have hIfin : Finite I := by
      have hsub : (I : Set ρ.range) ⊆ Set.range (fun n : Fin (orderOf T) => T ^ (n : ℕ)) := by
        intro y hy
        obtain ⟨n, rfl⟩ := hInat y hy
        exact ⟨⟨n % orderOf T, Nat.mod_lt _ hTfin.orderOf_pos⟩, pow_mod_orderOf T n⟩
      exact ((Set.finite_range _).subset hsub).to_subtype
    have hIiff : ∀ y, y ∈ I ↔ Φ * y * Φ⁻¹ ∈ I := by
      intro y
      refine ⟨hconjI y, fun hy => ?_⟩
      let c : I → I := fun z => ⟨Φ * z * Φ⁻¹, hconjI z z.2⟩
      have hc : Function.Injective c := by
        intro a b hab
        apply Subtype.ext
        have := congrArg Subtype.val hab
        simpa [c] using this
      obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hc) ⟨_, hy⟩
      have hzy : (z : ρ.range) = y := by
        have := congrArg Subtype.val hz
        simpa [c] using this
      exact hzy ▸ z.2
    let χ' : Fin N → ρ.range → Fbar ℓ := fun j y => e.repr (ρΓ y (e j)) j
    have hχpow : ∀ j (n : ℕ), χ' j (T ^ n) = L v₀ j ^ n := by
      intro j n
      show e.repr (ρΓ (T ^ n) (e j)) j = _
      rw [hTpow]
      simp
    refine hR ρ.range (Fbar ℓ) (Fin N → Fbar ℓ) ρΓ N H' I e χ' Φ (σ v₀)⁻¹ q₀.natDegree hN8
      hfin' hsolv' ?_ ?_ ?_ ?_ hIiff ?_ hq₀p (by rw [Fintype.card_fin]; exact hN2) hN3
      (by rw [Equiv.Perm.cycleType_inv]; exact hpc) W ?_
    · exact (Subgroup.zpowers_le).mpr (Subgroup.mem_map_of_mem _ (hτH v₀))
    · intro W' hW'
      apply hirr W'
      intro h _ x hx
      have := hW' (ρ.rangeRestrict h) x hx
      rwa [hρΓ, MonoidHom.coe_rangeRestrict, repGL_apply] at this
    · intro j y hy
      obtain ⟨n, rfl⟩ := hInat y hy
      rw [hTpow, hχpow]
    · intro j k hjk
      refine ⟨T, Subgroup.mem_zpowers T, ?_⟩
      have h1 := hχpow j 1
      have h2 := hχpow k 1
      rw [pow_one, pow_one] at h1 h2
      rw [h1, h2]
      exact fun h => hjk (hLinj v₀ h)
    · intro j y hy
      have hz : Φ⁻¹ * y * Φ ∈ I := by
        rw [hIiff]; simpa [mul_assoc] using hy
      obtain ⟨n, hn⟩ := hInat _ hz
      have hy' : y = T ^ (g i * n) := by
        rw [pow_mul, ← hTΦ, conj_pow, hn]; group
      rw [← hn, hy', hχpow, hχpow, pow_mul, ← hLσ]
      simp
    · intro h hh x hx
      obtain ⟨h0, hh0, rfl⟩ := Subgroup.mem_map.mp hh
      rw [hρΓ, MonoidHom.coe_rangeRestrict, repGL_apply]
      exact hW h0 hh0 x hx
  exact ⟨hirr, hpart2, hpart3⟩
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
