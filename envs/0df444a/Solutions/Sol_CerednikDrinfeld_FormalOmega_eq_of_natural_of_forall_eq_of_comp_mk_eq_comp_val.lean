-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.eq_of_natural_of_forall_eq_of_comp_mk_eq_comp_val
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/37887a14-8922-58e1-bfd9-ccd3495d6b37

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Theorems.Thm_CerednikDrinfeld_Onr_isDiscreteValuationRing_equalizer_and_irreducible
import Theorems.Thm_CerednikDrinfeld_Onr_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_eq_of_natural_of_forall_eq_of_comp_mk_eq_comp_val

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (n : ℕ) (Y : AlgFunctor 𝒪) (T : Scheme.{0})
    (F : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) →
      Y.obj B → (Spec (CommRingCat.of B) ⟶ T))
    (hFnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B') (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B)
      (y : Y.obj B),
      F B' hB' (φ.comp c) (Y.map φ y) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ F B hB c y)
    (F' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) →
      Y.obj B → (Spec (CommRingCat.of B) ⟶ T))
    (hF'nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B') (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B)
      (y : Y.obj B),
      F' B' hB' (φ.comp c) (Y.map φ y) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ F' B hB c y)
    (hagree : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (ψ : Onr →ₐ[𝒪] B)
      (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B),
      (∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), c (Ideal.Quotient.mk _ y) = ψ (y : Onr)) →
      ∀ y : Y.obj B, F B hB c y = F' B hB c y) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (y : Y.obj B),
      F B hB c y = F' B hB c y := by
  intro B _ _ hB c y
  classical

  have hπ0 : algebraMap 𝒪 Onr π ≠ 0 := by
    intro h0
    have hr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hr
    have h1 : ((r : ℕ) : Onr) = 0 := by
      have h2 := congrArg (algebraMap 𝒪 Onr) ha
      rw [map_mul, h0, mul_zero, map_natCast] at h2
      exact h2.symm
    exact (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero) h1

  obtain ⟨hdvr2, hirr2⟩ := CerednikDrinfeld.Onr.isDiscreteValuationRing_equalizer_and_irreducible 𝒪 π Onr
    hOnr_complete hOnr_max hπ0 (Fr.trans Fr)
  haveI : IsDiscreteValuationRing ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) := hdvr2
  haveI hff : Module.FaithfullyFlat ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr :=
    CerednikDrinfeld.Onr.faithfullyFlat ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) hdvr2 (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) hirr2 Onr Subtype.val_injective
      (by
        rw [show algebraMap ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) = algebraMap 𝒪 Onr π from rfl]
        exact hOnr_max.ne_top)

  letI algSB : Algebra ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B := ((c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))).toRingHom).toAlgebra
  have hsmul : ∀ (s : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (b : B), s • b = c ((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) s) * b := fun s b => rfl
  haveI : SMulCommClass ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) 𝒪 B := ⟨fun s o b => by
    rw [hsmul, hsmul, Algebra.smul_def, Algebra.smul_def]; ring⟩
  let B' : Type := B ⊗[↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr
  let ι : B →ₐ[𝒪] B' := Algebra.TensorProduct.includeLeft
  have hι : ∀ b : B, ι b = b ⊗ₜ[↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] (1 : Onr) := fun b => rfl
  let ψinf : Onr →ₐ[𝒪] B' :=
    { (Algebra.TensorProduct.includeRight : Onr →ₐ[↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] B').toRingHom with
      commutes' := fun o => by
        show (1 : B) ⊗ₜ[↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] (algebraMap 𝒪 Onr o) = algebraMap 𝒪 B' o
        rw [← ι.commutes o, hι, IsScalarTower.algebraMap_apply 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr o, Algebra.algebraMap_eq_smul_one,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', hsmul, mul_one, Ideal.Quotient.mkₐ_eq_mk]
        congr 1
        exact c.commutes o }
  have hψ : ∀ x : Onr, ψinf x = (1 : B) ⊗ₜ[↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] x := fun x => rfl
  have hc' : ∀ s : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), (ι.comp c) (Ideal.Quotient.mk _ s) = ψinf (s : Onr) := by
    intro s
    show ι (c (Ideal.Quotient.mk _ s)) = ψinf (s : Onr)
    rw [hι, hψ, show (s : Onr) = s • (1 : Onr) from (mul_one _).symm, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', hsmul, mul_one, Ideal.Quotient.mkₐ_eq_mk]
  have hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0 := by
    rw [← ι.commutes, ← map_pow, hB, map_zero]

  have key : Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ F B hB c y =
      Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ F' B hB c y := by
    rw [← hFnat B B' hB hB' ι c y, ← hF'nat B B' hB hB' ι c y]
    exact hagree B' hB' ψinf (ι.comp c) hc' (Y.map ι y)

  have hιalg : Spec.map (CommRingCat.ofHom ι.toRingHom) = Spec.map (CommRingCat.ofHom (algebraMap B B')) := by
    congr 2
  rw [hιalg] at key
  refine (AlgebraicGeometry.existsUnique_specMap_comp_eq_of_faithfullyFlat (B := B) (B' := B')
    (Spec.map (CommRingCat.ofHom (algebraMap B B')) ≫ F B hB c y) ?_).unique rfl key.symm
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 3
  apply RingHom.ext
  intro b
  show algebraMap B B' b ⊗ₜ[B] (1 : B') = (1 : B') ⊗ₜ[B] algebraMap B B' b
  rw [Algebra.algebraMap_eq_smul_one]
  exact TensorProduct.smul_tmul _ _ _

end S_CerednikDrinfeld_FormalOmega_eq_of_natural_of_forall_eq_of_comp_mk_eq_comp_val
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_eq_of_natural_of_forall_eq_of_comp_mk_eq_comp_val (solution)
