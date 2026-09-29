-- Prove2me | solution 1 for CochainCx.Bounded.finrank_HTot_tensor_eq_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/71b9e6fa-6934-56d7-b531-fedc5a7eafb7

import Theorems.Thm_DoubleComplex_nonempty_HTot_equiv_prod_of_levelwise_equiv_prod
import Theorems.Thm_DoubleComplex_subsingleton_HTot_of_rowContraction
import Theorems.Thm_DoubleComplex_subsingleton_HTot_of_colContraction
import Theorems.Thm_CochainCx_Bounded_exists_contractible_levelwise_equiv_prod
import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CochainCx_Bounded_finrank_HTot_tensor_eq_sum_mul

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgKunneth

open DoubleComplex CochainCx

variable {k : Type u} [Field k]

def prodDC (A B : DoubleComplex.Bounded k) : DoubleComplex.Bounded k where
  C p q := A.C p q × B.C p q
  dH p q := (A.dH p q).prodMap (B.dH p q)
  dV p q := (A.dV p q).prodMap (B.dV p q)
  dH_sq p q := by
    rw [LinearMap.prodMap_comp, A.dH_sq, B.dH_sq, LinearMap.prodMap_zero]
  dV_sq p q := by
    rw [LinearMap.prodMap_comp, A.dV_sq, B.dV_sq, LinearMap.prodMap_zero]
  dHV_comm p q := by
    apply LinearMap.ext; rintro ⟨a, b⟩
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply]
    exact Prod.ext (LinearMap.congr_fun (A.dHV_comm p q) a) (LinearMap.congr_fun (B.dHV_comm p q) b)
  N := max A.N B.N
  hBound p q h := by
    have hA : Subsingleton (A.C p q) := A.hBound p q (h.imp le_of_max_le_left le_of_max_le_left)
    have hB : Subsingleton (B.C p q) := B.hBound p q (h.imp le_of_max_le_right le_of_max_le_right)
    infer_instance

def zeroCx (V : ℕ → Type u) [∀ n, AddCommGroup (V n)] [∀ n, Module k (V n)] (N : ℕ)
    (hV : ∀ n, N ≤ n → Subsingleton (V n)) : CochainCx.Bounded k where
  X := V
  d _ := 0
  d_sq _ := by simp
  N := N
  hBound := hV

theorem subsingleton_H (C : CochainCx.Bounded k) (n : ℕ) (hn : C.N ≤ n) : Subsingleton (C.H n) := by
  haveI := C.hBound n hn
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show y = 0 from Subsingleton.elim _ _, Submodule.Quotient.mk_zero]

def HCx (C : CochainCx.Bounded k) : CochainCx.Bounded k :=
  zeroCx (fun p => C.H p) C.N (fun n hn => subsingleton_H C n hn)

scoped instance fintypeDiag (n : ℕ) : Fintype (Diag n) :=
  Fintype.ofEquiv (Fin (n + 1))
    { toFun := fun j => ⟨(j.1, n - j.1), by have := j.2; simp; omega⟩
      invFun := fun i => ⟨i.1.1, by have := i.2; omega⟩
      left_inv := fun j => by ext; rfl
      right_inv := fun i => by
        obtain ⟨⟨p, q⟩, h⟩ := i
        simp only at h
        apply Subtype.ext; simp only; ext <;> simp; omega }

theorem HTot_zero (C D : CochainCx.Bounded k) (hC : ∀ p, C.d p = 0) (hD : ∀ q, D.d q = 0) (n : ℕ) :
    Nonempty (HTot (C.tensor D) n ≃ₗ[k] Tot (C.tensor D) n) := by
  have hz : ∀ m, dTot (C.tensor D) m = 0 := by
    intro m
    refine LinearMap.ext fun c => funext fun ⟨⟨pp, q⟩, h⟩ => ?_
    simp only [LinearMap.zero_apply, Pi.zero_apply]
    match pp, q, h with
    | 0, 0, h => omega
    | 0, q' + 1, h =>
      rw [dTot_apply_zero_succ]
      change (D.d q').lTensor (C.X 0) _ = 0
      rw [hD, LinearMap.lTensor_zero, LinearMap.zero_apply]
    | p' + 1, 0, h =>
      rw [dTot_apply_succ_zero]
      change (C.d p').rTensor (D.X 0) _ = 0
      rw [hC, LinearMap.rTensor_zero, LinearMap.zero_apply]
    | p' + 1, q' + 1, h =>
      rw [dTot_apply_succ_succ]
      change (C.d p').rTensor (D.X (q' + 1)) _ + ((-1 : ℤ) ^ (p' + 1)) • (D.d q').lTensor (C.X (p' + 1)) _ = 0
      rw [hC, hD, LinearMap.rTensor_zero, LinearMap.lTensor_zero, LinearMap.zero_apply, LinearMap.zero_apply,
        zero_add]
      exact zsmul_zero _
  have hB : HTotB (C.tensor D) n = ⊥ := by
    cases n with
    | zero => rfl
    | succ m =>
      change (LinearMap.range (dTot (C.tensor D) m)).comap (LinearMap.ker (dTot (C.tensor D) (m + 1))).subtype = ⊥
      rw [hz m, LinearMap.range_zero, Submodule.comap_bot, LinearMap.ker_eq_bot]
      exact Subtype.val_injective
  have hK : LinearMap.ker (dTot (C.tensor D) n) = ⊤ := by rw [hz n, LinearMap.ker_zero]
  exact ⟨Submodule.quotEquivOfEqBot _ hB ≪≫ₗ LinearEquiv.ofEq _ _ hK ≪≫ₗ Submodule.topEquiv⟩

set_option maxHeartbeats 12800000 in
theorem main (C D : CochainCx.Bounded k)
    (hC : ∀ p, Module.Finite k (C.H p)) (hD : ∀ q, Module.Finite k (D.H q)) (n : ℕ) :
    Module.Finite k (HTot (C.tensor D) n) ∧
      Module.finrank k (HTot (C.tensor D) n) = ∑ i ∈ Finset.range (n + 1), C.hfinrank i * D.hfinrank (n - i) := by
  classical
  obtain ⟨E, σ, hσ0, hσ, e, he⟩ := CochainCx.Bounded.exists_contractible_levelwise_equiv_prod C
  obtain ⟨E', σ', hσ0', hσ', e', he'⟩ := CochainCx.Bounded.exists_contractible_levelwise_equiv_prod D
  let HC := HCx C
  let HD := HCx D
  let HH := HC.tensor HD
  let HE := HC.tensor E'
  let EH := E.tensor HD
  let EE := E.tensor E'
  let R2 := prodDC EH EE
  let R1 := prodDC HE R2

  let e1 : ∀ p q : ℕ, (C.tensor D).C p q ≃ₗ[k] (HH.C p q × R1.C p q) := fun p q =>
    (TensorProduct.congr (e p) (e' q)) ≪≫ₗ (TensorProduct.prodLeft k k (C.H p) (E.X p) (D.H q × E'.X q)) ≪≫ₗ
      ((TensorProduct.prodRight k k (C.H p) (D.H q) (E'.X q)).prodCongr
        (TensorProduct.prodRight k k (E.X p) (D.H q) (E'.X q))) ≪≫ₗ
      (LinearEquiv.prodAssoc k _ _ _)
  have he1 : ∀ (p q : ℕ) (a : C.X p) (b : D.X q), e1 p q (a ⊗ₜ[k] b) =
      ((e p a).1 ⊗ₜ (e' q b).1, ((e p a).1 ⊗ₜ (e' q b).2, ((e p a).2 ⊗ₜ (e' q b).1, (e p a).2 ⊗ₜ (e' q b).2))) := by
    intro p q a b
    rfl

  have hH1 : ∀ (p q : ℕ) (x : (C.tensor D).C p q),
      e1 (p + 1) q ((C.tensor D).dH p q x) = (HH.dH p q (e1 p q x).1, R1.dH p q (e1 p q x).2) := by
    intro p q x
    have : ((e1 (p + 1) q).toLinearMap ∘ₗ (C.tensor D).dH p q) =
        ((HH.dH p q).prodMap (R1.dH p q)) ∘ₗ (e1 p q).toLinearMap := by
      apply TensorProduct.ext'
      intro a b
      change e1 (p + 1) q ((C.d p).rTensor (D.X q) (a ⊗ₜ[k] b)) = (HH.dH p q (e1 p q (a ⊗ₜ b)).1, R1.dH p q (e1 p q (a ⊗ₜ b)).2)
      rw [LinearMap.rTensor_tmul, he1, he1, he]
      change ((0 : C.H (p + 1)) ⊗ₜ[k] (e' q b).1, ((0 : C.H (p + 1)) ⊗ₜ[k] (e' q b).2,
          (E.d p (e p a).2 ⊗ₜ[k] (e' q b).1, E.d p (e p a).2 ⊗ₜ[k] (e' q b).2))) =
        ((0 : C.H p →ₗ[k] C.H (p + 1)).rTensor _ ((e p a).1 ⊗ₜ[k] (e' q b).1),
          ((0 : C.H p →ₗ[k] C.H (p + 1)).rTensor _ ((e p a).1 ⊗ₜ[k] (e' q b).2),
            ((E.d p).rTensor _ ((e p a).2 ⊗ₜ[k] (e' q b).1), (E.d p).rTensor _ ((e p a).2 ⊗ₜ[k] (e' q b).2))))
      simp only [LinearMap.rTensor_tmul, LinearMap.zero_apply]
    exact LinearMap.congr_fun this x
  have hV1 : ∀ (p q : ℕ) (x : (C.tensor D).C p q),
      e1 p (q + 1) ((C.tensor D).dV p q x) = (HH.dV p q (e1 p q x).1, R1.dV p q (e1 p q x).2) := by
    intro p q x
    have : ((e1 p (q + 1)).toLinearMap ∘ₗ (C.tensor D).dV p q) =
        ((HH.dV p q).prodMap (R1.dV p q)) ∘ₗ (e1 p q).toLinearMap := by
      apply TensorProduct.ext'
      intro a b
      change e1 p (q + 1) ((D.d q).lTensor (C.X p) (a ⊗ₜ[k] b)) = (HH.dV p q (e1 p q (a ⊗ₜ b)).1, R1.dV p q (e1 p q (a ⊗ₜ b)).2)
      rw [LinearMap.lTensor_tmul, he1, he1, he']
      change ((e p a).1 ⊗ₜ[k] (0 : D.H (q + 1)), ((e p a).1 ⊗ₜ[k] E'.d q (e' q b).2,
          ((e p a).2 ⊗ₜ[k] (0 : D.H (q + 1)), (e p a).2 ⊗ₜ[k] E'.d q (e' q b).2))) =
        ((0 : D.H q →ₗ[k] D.H (q + 1)).lTensor _ ((e p a).1 ⊗ₜ[k] (e' q b).1),
          ((E'.d q).lTensor _ ((e p a).1 ⊗ₜ[k] (e' q b).2),
            ((0 : D.H q →ₗ[k] D.H (q + 1)).lTensor _ ((e p a).2 ⊗ₜ[k] (e' q b).1), (E'.d q).lTensor _ ((e p a).2 ⊗ₜ[k] (e' q b).2))))
      simp only [LinearMap.lTensor_tmul, LinearMap.zero_apply]
    exact LinearMap.congr_fun this x

  obtain ⟨E1⟩ := DoubleComplex.nonempty_HTot_equiv_prod_of_levelwise_equiv_prod (C.tensor D) HH R1 e1 hH1 hV1 n
  obtain ⟨E2⟩ := DoubleComplex.nonempty_HTot_equiv_prod_of_levelwise_equiv_prod R1 HE R2
    (fun p q => LinearEquiv.refl k _) (fun _ _ _ => rfl) (fun _ _ _ => rfl) n
  obtain ⟨E3⟩ := DoubleComplex.nonempty_HTot_equiv_prod_of_levelwise_equiv_prod R2 EH EE
    (fun p q => LinearEquiv.refl k _) (fun _ _ _ => rfl) (fun _ _ _ => rfl) n

  have hidE : σ 0 ∘ₗ E.d 0 = LinearMap.id := LinearMap.ext hσ0
  have hidE' : σ' 0 ∘ₗ E'.d 0 = LinearMap.id := LinearMap.ext hσ0'
  have hsumE : ∀ p, σ (p + 1) ∘ₗ E.d (p + 1) + E.d p ∘ₗ σ p = LinearMap.id := fun p => LinearMap.ext (hσ p)
  have hsumE' : ∀ p, σ' (p + 1) ∘ₗ E'.d (p + 1) + E'.d p ∘ₗ σ' p = LinearMap.id := fun p => LinearMap.ext (hσ' p)
  haveI hHE : Subsingleton (HTot HE n) := by
    refine DoubleComplex.subsingleton_HTot_of_colContraction HE (fun p q => (σ' q).lTensor (C.H p)) ?_ ?_ ?_ n
    · intro p x
      change (σ' 0).lTensor (C.H p) ((E'.d 0).lTensor (C.H p) x) = x
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hidE', LinearMap.lTensor_id, LinearMap.id_apply]
    · intro p q x
      change (σ' (q + 1)).lTensor (C.H p) ((E'.d (q + 1)).lTensor (C.H p) x) + (E'.d q).lTensor (C.H p) ((σ' q).lTensor (C.H p) x) = x
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp,
        ← LinearMap.add_apply, ← LinearMap.lTensor_add, hsumE', LinearMap.lTensor_id, LinearMap.id_apply]
    · intro p q x
      change (σ' q).lTensor (C.H (p + 1)) ((0 : C.H p →ₗ[k] C.H (p + 1)).rTensor _ x) =
        (0 : C.H p →ₗ[k] C.H (p + 1)).rTensor _ ((σ' q).lTensor (C.H p) x)
      rw [LinearMap.rTensor_zero, LinearMap.rTensor_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  haveI hEH : Subsingleton (HTot EH n) := by
    refine DoubleComplex.subsingleton_HTot_of_rowContraction EH (fun p q => (σ p).rTensor (D.H q)) ?_ ?_ ?_ n
    · intro q x
      change (σ 0).rTensor (D.H q) ((E.d 0).rTensor (D.H q) x) = x
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hidE, LinearMap.rTensor_id, LinearMap.id_apply]
    · intro p q x
      change (σ (p + 1)).rTensor (D.H q) ((E.d (p + 1)).rTensor (D.H q) x) + (E.d p).rTensor (D.H q) ((σ p).rTensor (D.H q) x) = x
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp,
        ← LinearMap.add_apply, ← LinearMap.rTensor_add, hsumE, LinearMap.rTensor_id, LinearMap.id_apply]
    · intro p q x
      change (σ p).rTensor (D.H (q + 1)) ((0 : D.H q →ₗ[k] D.H (q + 1)).lTensor _ x) =
        (0 : D.H q →ₗ[k] D.H (q + 1)).lTensor _ ((σ p).rTensor (D.H q) x)
      rw [LinearMap.lTensor_zero, LinearMap.lTensor_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  haveI hEE : Subsingleton (HTot EE n) := by
    refine DoubleComplex.subsingleton_HTot_of_rowContraction EE (fun p q => (σ p).rTensor (E'.X q)) ?_ ?_ ?_ n
    · intro q x
      change (σ 0).rTensor (E'.X q) ((E.d 0).rTensor (E'.X q) x) = x
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hidE, LinearMap.rTensor_id, LinearMap.id_apply]
    · intro p q x
      change (σ (p + 1)).rTensor (E'.X q) ((E.d (p + 1)).rTensor (E'.X q) x) + (E.d p).rTensor (E'.X q) ((σ p).rTensor (E'.X q) x) = x
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp,
        ← LinearMap.add_apply, ← LinearMap.rTensor_add, hsumE, LinearMap.rTensor_id, LinearMap.id_apply]
    · intro p q x
      change (σ p).rTensor (E'.X (q + 1)) ((E'.d q).lTensor _ x) = (E'.d q).lTensor _ ((σ p).rTensor (E'.X q) x)
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor]
  haveI hR2 : Subsingleton (HTot R2 n) := E3.toEquiv.subsingleton_congr.mpr inferInstance
  haveI hR1 : Subsingleton (HTot R1 n) := E2.toEquiv.subsingleton_congr.mpr inferInstance

  obtain ⟨E4⟩ := HTot_zero HC HD (fun _ => rfl) (fun _ => rfl) n
  haveI : ∀ i : Diag n, Module.Finite k (HH.C i.1.1 i.1.2) := fun i => by
    change Module.Finite k (C.H i.1.1 ⊗[k] D.H i.1.2); infer_instance
  haveI hfinTot : Module.Finite k (Tot HH n) := Module.Finite.pi
  haveI hfinHH : Module.Finite k (HTot HH n) := Module.Finite.equiv E4.symm
  have hrkTot : Module.finrank k (Tot HH n) = ∑ i ∈ Finset.range (n + 1), C.hfinrank i * D.hfinrank (n - i) := by
    change Module.finrank k (∀ i : Diag n, C.H i.1.1 ⊗[k] D.H i.1.2) = _
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_tensorProduct]
    rw [← Fin.sum_univ_eq_sum_range]
    exact (Fintype.sum_equiv (Equiv.ofBijective (fun i : Diag n => (⟨i.1.1, by have := i.2; omega⟩ : Fin (n + 1)))
      ⟨fun i j hij => by
        obtain ⟨⟨a, b⟩, ha⟩ := i; obtain ⟨⟨c, d⟩, hc⟩ := j
        simp only [Fin.mk.injEq] at hij
        apply Subtype.ext; simp only at ha hc ⊢; ext <;> simp <;> omega,
       fun j => ⟨⟨(j.1, n - j.1), by have := j.2; simp; omega⟩, rfl⟩⟩) _ _
      (fun i => by
        obtain ⟨⟨a, b⟩, hab⟩ := i
        simp only [Equiv.ofBijective_apply]
        have : b = n - a := by simp at hab; omega
        subst this
        rfl))

  haveI : Module.Finite k (HTot HH n × HTot R1 n) := inferInstance
  refine ⟨Module.Finite.equiv E1.symm, ?_⟩
  rw [E1.finrank_eq, Module.finrank_prod, Module.finrank_zero_of_subsingleton (M := HTot R1 n), add_zero,
    E4.finrank_eq, hrkTot]

end AlgKunneth
p2m_reactivate "P2MW.S_CochainCx_Bounded_finrank_HTot_tensor_eq_sum_mul.AlgKunneth"

theorem solution
    {k : Type u} [Field k] (C D : CochainCx.Bounded k)
    (hC : ∀ p, Module.Finite k (C.H p)) (hD : ∀ q, Module.Finite k (D.H q)) (n : ℕ) :
    Module.Finite k (DoubleComplex.HTot (C.tensor D) n) ∧
      Module.finrank k (DoubleComplex.HTot (C.tensor D) n) =
        ∑ i ∈ Finset.range (n + 1), C.hfinrank i * D.hfinrank (n - i) :=
  AlgKunneth.main C D hC hD n

end S_CochainCx_Bounded_finrank_HTot_tensor_eq_sum_mul
end P2MW
export P2MW.S_CochainCx_Bounded_finrank_HTot_tensor_eq_sum_mul (solution)
