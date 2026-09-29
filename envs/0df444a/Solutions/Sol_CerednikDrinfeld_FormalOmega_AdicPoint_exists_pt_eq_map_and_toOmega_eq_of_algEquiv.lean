-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.AdicPoint.exists_pt_eq_map_and_toOmega_eq_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4cb613d6-c4e8-5839-8631-36e96b332956

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_pt_eq_map_and_toOmega_eq_of_algEquiv

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace G1

variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
variable {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B']

theorem map_comp' {B₃ : Type} [CommRing B₃] [Algebra 𝒪 B₃] (f : B →ₐ[𝒪] B') (g : B' →ₐ[𝒪] B₃) (d : DeligneDatum (K := K₀) π B) :
    DeligneDatum.map π (g.comp f) d = DeligneDatum.map π g (DeligneDatum.map π f d) :=
  (Omega K₀ π).map_comp f g d

theorem map_id' (d : DeligneDatum (K := K₀) π B) : DeligneDatum.map π (AlgHom.id 𝒪 B) d = d :=
  (Omega K₀ π).map_id d

theorem mem_lineBaseChange_iff_of_bijective (f : B →ₐ[𝒪] B') (hf : Function.Bijective f) (M : FullLattice 𝒪 K₀)
    (N : Submodule B (latticeBaseChange 𝒪 K₀ B M)) (v : latticeBaseChange 𝒪 K₀ B M) :
    LinearMap.rTensor (↥M.1) f.toLinearMap v ∈ lineBaseChange (K := K₀) f M N ↔ v ∈ N := by

  let e : B ≃ₐ[𝒪] B' := AlgEquiv.ofBijective f hf
  have hef : ∀ b, e b = f b := fun _ => rfl
  let φ := LinearMap.rTensor (↥M.1) f.toLinearMap
  let ψ := LinearMap.rTensor (↥M.1) (e.symm : B' →ₐ[𝒪] B).toLinearMap
  have hψφ : ∀ w, ψ (φ w) = w := by
    intro w
    show (ψ.comp φ) w = w
    rw [show ψ.comp φ = LinearMap.rTensor (↥M.1) ((e.symm : B' →ₐ[𝒪] B).toLinearMap.comp f.toLinearMap) from
      (LinearMap.rTensor_comp _ _ _).symm]
    have : (e.symm : B' →ₐ[𝒪] B).toLinearMap.comp f.toLinearMap = LinearMap.id := by
      apply LinearMap.ext; intro b; show e.symm (f b) = b; rw [← hef]; exact e.symm_apply_apply b
    rw [this, LinearMap.rTensor_id]; rfl
  have hφψ : ∀ w, φ (ψ w) = w := by
    intro w
    show (φ.comp ψ) w = w
    rw [show φ.comp ψ = LinearMap.rTensor (↥M.1) (f.toLinearMap.comp (e.symm : B' →ₐ[𝒪] B).toLinearMap) from
      (LinearMap.rTensor_comp _ _ _).symm]
    have : f.toLinearMap.comp (e.symm : B' →ₐ[𝒪] B).toLinearMap = LinearMap.id := by
      apply LinearMap.ext; intro b; show f (e.symm b) = b; rw [← hef]; exact e.apply_symm_apply b
    rw [this, LinearMap.rTensor_id]; rfl

  have hφs : ∀ (b : B) (w : latticeBaseChange 𝒪 K₀ B M), φ (b • w) = f b • φ w := by
    intro b w
    induction w using TensorProduct.induction_on with
    | zero => simp [φ]
    | tmul x m => simp [φ, TensorProduct.smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have hψs : ∀ (b : B') (w : latticeBaseChange 𝒪 K₀ B' M), ψ (b • w) = e.symm b • ψ w := by
    intro b w
    induction w using TensorProduct.induction_on with
    | zero => simp [ψ]
    | tmul x m => simp [ψ, TensorProduct.smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  constructor
  · intro h

    have hsub : ∀ w ∈ lineBaseChange (K := K₀) f M N, ψ w ∈ N := by
      intro w hw
      rw [lineBaseChange] at hw
      induction hw using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨u0, hu0, rfl⟩ := hu
        show ψ (φ u0) ∈ N
        rw [hψφ]; exact hu0
      | zero => rw [map_zero]; exact zero_mem _
      | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
      | smul b u _ hu => rw [hψs]; exact N.smul_mem _ hu
    have := hsub _ h
    rwa [show ψ (LinearMap.rTensor (↥M.1) f.toLinearMap v) = v from hψφ v] at this
  · intro h
    rw [lineBaseChange]
    exact Submodule.subset_span ⟨v, h, rfl⟩

end G1

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R] (C : Type) [Field C] [Algebra R C]
    (τ : R ≃ₐ[𝒪] R) (s : C ≃+* C) (hτs : ∀ a : R, algebraMap R C (τ a) = s (algebraMap R C a))
    (τn : ∀ k : ℕ, modPow π R k →ₐ[𝒪] modPow π R k)
    (hτn : ∀ (k : ℕ) (a : R), τn k (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) a) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) (τ a))
    (x : AdicPoint K₀ π R) :
    ∃ x' : AdicPoint K₀ π R, (∀ k : ℕ, x'.pt k = DeligneDatum.map π (τn k) (x.pt k)) ∧
      x'.toOmega C = s (x.toOmega C) := by
  classical

  have hmk : ∀ (k : ℕ) (b : R), modPowTransition π R k (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b := fun k b => rfl
  have hcomm : ∀ k : ℕ, (modPowTransition π R k).comp (τn (k + 1)) = (τn k).comp (modPowTransition π R k) := by
    intro k
    apply AlgHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    show modPowTransition π R k (τn (k + 1) (Ideal.Quotient.mk _ a)) = τn k (modPowTransition π R k (Ideal.Quotient.mk _ a))
    rw [hτn, hmk, hmk, hτn]

  have hτI : ∀ (k : ℕ) (a : R), a ∈ Ideal.span {algebraMap 𝒪 R π ^ (k + 1)} → τ.symm a ∈ Ideal.span {algebraMap 𝒪 R π ^ (k + 1)} := by
    intro k a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, AlgEquiv.commutes]
    exact Ideal.mem_span_singleton'.2 ⟨τ.symm c, rfl⟩
  have hbij : ∀ k : ℕ, Function.Bijective (τn k) := by
    intro k
    constructor
    · intro u v h
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
      rw [hτn, hτn, Ideal.Quotient.eq] at h
      rw [Ideal.Quotient.eq]
      have := hτI k _ h
      rwa [map_sub, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply] at this
    · intro v
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
      exact ⟨Ideal.Quotient.mk _ (τ.symm b), by rw [hτn, AlgEquiv.apply_symm_apply]⟩

  let x' : AdicPoint K₀ π R :=
    { pt := fun k => DeligneDatum.map π (τn k) (x.pt k)
      compat := fun k => by
        show DeligneDatum.map π (modPowTransition π R k) (DeligneDatum.map π (τn (k + 1)) (x.pt (k + 1))) =
          DeligneDatum.map π (τn k) (x.pt k)
        rw [← G1.map_comp', hcomm, G1.map_comp', x.compat] }
  refine ⟨x', fun k => rfl, ?_⟩

  have hcoord : ∀ (k : ℕ) (w : Fin 2 → R), coordToTensor K₀ π R k (fun i => τ (w i)) =
      LinearMap.rTensor _ (τn k).toLinearMap (coordToTensor K₀ π R k w) := by
    intro k w
    simp only [coordToTensor, map_sum, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, hτn]

  have hstd : ∀ w : Fin 2 → R, (fun i => τ (w i)) ∈ x'.stdLine ↔ w ∈ x.stdLine := by
    intro w
    rw [AdicPoint.mem_stdLine_iff, AdicPoint.mem_stdLine_iff]
    refine forall_congr' fun k => ?_
    show coordToTensor K₀ π R k (fun i => τ (w i)) ∈ lineBaseChange (K := K₀) (τn k) _ ((x.pt k).line _) ↔ _
    rw [hcoord]
    exact G1.mem_lineBaseChange_iff_of_bijective (τn k) (hbij k) _ _ _

  let σ : (Fin 2 → C) → (Fin 2 → C) := fun v i => s (v i)
  let σ' : (Fin 2 → C) → (Fin 2 → C) := fun v i => s.symm (v i)
  have hσσ' : ∀ v, σ (σ' v) = v := fun v => funext fun i => s.apply_symm_apply _
  have hσ'σ : ∀ v, σ' (σ v) = v := fun v => funext fun i => s.symm_apply_apply _
  have hσ_add : ∀ u v, σ (u + v) = σ u + σ v := fun u v => funext fun i => map_add s _ _
  have hσ_smul : ∀ (c : C) u, σ (c • u) = s c • σ u := fun c u => funext fun i => by simp [σ, smul_eq_mul, map_mul]
  have hσ'_add : ∀ u v, σ' (u + v) = σ' u + σ' v := fun u v => funext fun i => map_add s.symm _ _
  have hσ'_smul : ∀ (c : C) u, σ' (c • u) = s.symm c • σ' u := fun c u => funext fun i => by simp [σ', smul_eq_mul, map_mul]

  have hgen : ∀ v : Fin 2 → C, v ∈ (fun w : Fin 2 → R => fun i => algebraMap R C (w i)) '' (x'.stdLine : Set (Fin 2 → R)) ↔
      σ' v ∈ (fun w : Fin 2 → R => fun i => algebraMap R C (w i)) '' (x.stdLine : Set (Fin 2 → R)) := by
    intro v
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨fun i => τ.symm (w i), ?_, ?_⟩
      · apply (hstd (fun i => τ.symm (w i))).1
        have : (fun i => τ (τ.symm (w i))) = w := funext fun i => τ.apply_symm_apply (w i)
        rw [this]; exact hw
      · funext i; show algebraMap R C (τ.symm (w i)) = s.symm (algebraMap R C (w i))
        apply s.injective; rw [← hτs, AlgEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    · rintro ⟨w, hw, hwv⟩
      refine ⟨fun i => τ (w i), (hstd w).2 hw, ?_⟩
      funext i
      have h1 : algebraMap R C (w i) = s.symm (v i) := congrFun hwv i
      show algebraMap R C (τ (w i)) = v i
      rw [hτs, h1]; exact s.apply_symm_apply _
  have hline : ∀ v : Fin 2 → C, v ∈ x'.lineC C ↔ σ' v ∈ x.lineC C := by
    intro v
    constructor
    · intro hv
      unfold AdicPoint.lineC at hv ⊢
      induction hv using Submodule.span_induction with
      | mem u hu => exact Submodule.subset_span ((hgen u).1 hu)
      | zero => show σ' 0 ∈ _; rw [show σ' 0 = 0 from funext fun i => map_zero s.symm]; exact zero_mem _
      | add u w _ _ hu hw => rw [hσ'_add]; exact add_mem hu hw
      | smul c u _ hu => rw [hσ'_smul]; exact Submodule.smul_mem _ _ hu
    · intro hv
      have key : ∀ u ∈ x.lineC C, σ u ∈ x'.lineC C := by
        intro u hu
        unfold AdicPoint.lineC at hu ⊢
        induction hu using Submodule.span_induction with
        | mem u hu => exact Submodule.subset_span ((hgen (σ u)).2 (by rw [hσ'σ]; exact hu))
        | zero => show σ 0 ∈ _; rw [show σ 0 = 0 from funext fun i => map_zero s]; exact zero_mem _
        | add u w _ _ hu hw => rw [hσ_add]; exact add_mem hu hw
        | smul c u _ hu => rw [hσ_smul]; exact Submodule.smul_mem _ _ hu
      have := key _ hv
      rwa [hσσ'] at this

  have hvec : ∀ z : C, σ' (![z, 1] : Fin 2 → C) = ![s.symm z, 1] := by
    intro z; funext i; fin_cases i <;> simp [σ']
  have hiff : (∃! z : C, (![z, 1] : Fin 2 → C) ∈ x'.lineC C) ↔ (∃! z : C, (![z, 1] : Fin 2 → C) ∈ x.lineC C) := by
    have hmemiff : ∀ z : C, (![z, 1] : Fin 2 → C) ∈ x'.lineC C ↔ (![s.symm z, 1] : Fin 2 → C) ∈ x.lineC C := by
      intro z; rw [hline, hvec]
    constructor
    · rintro ⟨z, hz, huniq⟩
      refine ⟨s.symm z, (hmemiff z).1 hz, fun y hy => ?_⟩
      have h1 : (![s y, 1] : Fin 2 → C) ∈ x'.lineC C := by rw [hmemiff, s.symm_apply_apply]; exact hy
      have := huniq (s y) h1
      rw [← this, s.symm_apply_apply]
    · rintro ⟨z, hz, huniq⟩
      have hz' : (![s z, 1] : Fin 2 → C) ∈ x'.lineC C := by rw [hmemiff, s.symm_apply_apply]; exact hz
      refine ⟨s z, hz', fun y hy => ?_⟩
      have := huniq (s.symm y) ((hmemiff y).1 hy)
      rw [← this, s.apply_symm_apply]
  by_cases hx : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ x.lineC C
  · have hx' := hiff.2 hx
    have hmem' := x'.vecCons_toOmega_mem C hx'
    have hmem : (![s (x.toOmega C), 1] : Fin 2 → C) ∈ x'.lineC C := by
      rw [hline, hvec, s.symm_apply_apply]; exact x.vecCons_toOmega_mem C hx
    exact hx'.unique hmem' hmem
  · have hx' : ¬ ∃! z : C, (![z, 1] : Fin 2 → C) ∈ x'.lineC C := fun h => hx (hiff.1 h)
    rw [AdicPoint.toOmega, dif_neg hx', AdicPoint.toOmega, dif_neg hx, map_zero]

end

end S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_pt_eq_map_and_toOmega_eq_of_algEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_pt_eq_map_and_toOmega_eq_of_algEquiv (solution)
