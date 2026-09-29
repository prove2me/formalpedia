-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_hondaSystem_addEquiv_smul_eq_map_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/338ff728-80c6-51c4-97c0-11af025ca79d

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Theorems.Thm_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge
import Theorems.Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_wittHomMap_convMul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_hondaSystem_addEquiv_smul_eq_map_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open scoped PadicInt TensorProduct

namespace S17KHonda

open WithConv Deformation

variable (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] (ZMod p)]
variable (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Coalgebra.IsCocomm ℤ_[p] H]

noncomputable def σ (φ : H →ₐc[ℤ_[p]] H) :
    (ZMod p) ⊗[ℤ_[p]] H →ₐc[ZMod p] (ZMod p) ⊗[ℤ_[p]] H :=
  Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) φ

variable {p H}

theorem σ_tmul (φ : H →ₐc[ℤ_[p]] H) (s : ZMod p) (h : H) :
    σ p H φ (s ⊗ₜ[ℤ_[p]] h) = s ⊗ₜ[ℤ_[p]] φ h := rfl

theorem σ_comp (φ ψ : H →ₐc[ℤ_[p]] H) : σ p H (φ.comp ψ) = (σ p H φ).comp (σ p H ψ) := by
  apply BialgHom.coe_fn_injective
  funext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s h => rfl
  | add x y hx hy =>
    rw [map_add, hx, hy]
    exact (map_add _ x y).symm

theorem σ_id : σ p H (BialgHom.id ℤ_[p] H) = BialgHom.id (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H) := by
  apply BialgHom.coe_fn_injective
  funext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s h => rfl
  | add x y hx hy =>
    rw [map_add, hx, hy]
    exact (map_add _ x y).symm

set_option maxHeartbeats 3200000 in

theorem σ_convMul (φ ψ : H →ₐc[ℤ_[p]] H) :
    σ p H (toConv φ * toConv ψ).ofConv = (toConv (σ p H φ) * toConv (σ p H ψ)).ofConv := by
  classical
  apply BialgHom.coe_algHom_injective
  apply Algebra.TensorProduct.ext'
  intro s h

  rw [show ((σ p H (toConv φ * toConv ψ).ofConv : _ →ₐc[ZMod p] _) : _ →ₐ[ZMod p] _) (s ⊗ₜ[ℤ_[p]] h)
      = s ⊗ₜ[ℤ_[p]] ((toConv φ * toConv ψ).ofConv : H →ₐc[ℤ_[p]] H) h from rfl]
  rw [show ((toConv φ * toConv ψ).ofConv : H →ₐc[ℤ_[p]] H) h
      = ((toConv (φ : H →ₐ[ℤ_[p]] H) * toConv (ψ : H →ₐ[ℤ_[p]] H)).ofConv : H →ₐ[ℤ_[p]] H) h from by
        rw [← BialgHom.toAlgHom_convMul]; rfl]
  have eR : (((toConv (σ p H φ) * toConv (σ p H ψ)).ofConv :
        (ZMod p) ⊗[ℤ_[p]] H →ₐc[ZMod p] (ZMod p) ⊗[ℤ_[p]] H) : (ZMod p) ⊗[ℤ_[p]] H →ₐ[ZMod p] (ZMod p) ⊗[ℤ_[p]] H)
      = (toConv (σ p H φ : (ZMod p) ⊗[ℤ_[p]] H →ₐ[ZMod p] (ZMod p) ⊗[ℤ_[p]] H) *
          toConv (σ p H ψ : (ZMod p) ⊗[ℤ_[p]] H →ₐ[ZMod p] (ZMod p) ⊗[ℤ_[p]] H)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (toConv (σ p H φ)) (toConv (σ p H ψ)))
  rw [eR]
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]
  let 𝓡 := Coalgebra.Repr.arbitrary ℤ_[p] h
  conv_lhs => rw [← 𝓡.eq]
  conv_rhs => rw [← 𝓡.eq]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
    Algebra.TensorProduct.lift_tmul, ofConv_toConv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BialgHom.coe_toAlgHom, BialgHom.coe_toAlgHom, BialgHom.coe_toAlgHom, BialgHom.coe_toAlgHom,
    σ_tmul, σ_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem map_convMul {R : Type} [CommRing R] {q : ℕ} [Fact q.Prime]
    {B : Type} [CommRing B] [Bialgebra R B] [Coalgebra.IsCocomm R B]
    (Φ Ψ : WithConv (B →ₐc[R] B)) (z : DieudonneModule R q B) :
    DieudonneModule.map R q (Φ * Ψ).ofConv z =
      DieudonneModule.map R q Φ.ofConv z + DieudonneModule.map R q Ψ.ofConv z := by
  induction z using DieudonneModule.induction_on with
  | ih n x => rw [DieudonneModule.map_of, DieudonneModule.map_of, DieudonneModule.map_of,
      wittHomMap_convMul, map_add]

variable (p H)
variable {k : Type} [Field k] (θ : k → (H →ₐc[ℤ_[p]] H))

noncomputable def act (a : k) :
    DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) →+ DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) :=
  DieudonneModule.map (ZMod p) p (σ p H (θ a))

variable {p H θ}

theorem act_apply (a : k) (z) : act p H θ a z = DieudonneModule.map (ZMod p) p (σ p H (θ a)) z := rfl

theorem act_mul (hθ_mul : ∀ a b : k, θ (a * b) = (θ a).comp (θ b)) (a b : k) (z) :
    act p H θ (a * b) z = act p H θ a (act p H θ b z) := by
  rw [act_apply, act_apply, act_apply, hθ_mul, σ_comp, DieudonneModule.map_comp]

theorem act_one (hθ_one : θ 1 = BialgHom.id ℤ_[p] H) (z) : act p H θ 1 z = z := by
  rw [act_apply, hθ_one, σ_id, DieudonneModule.map_id]

theorem act_add
    (hθ_add : ∀ a b : k, toConv (θ (a + b) : H →ₐ[ℤ_[p]] H) =
      toConv (θ a : H →ₐ[ℤ_[p]] H) * toConv (θ b : H →ₐ[ℤ_[p]] H)) (a b : k) (z) :
    act p H θ (a + b) z = act p H θ a z + act p H θ b z := by
  have hab : θ (a + b) = (toConv (θ a) * toConv (θ b)).ofConv := by
    apply BialgHom.coe_algHom_injective
    have := hθ_add a b
    rw [← BialgHom.toAlgHom_convMul] at this
    exact toConv_injective this
  rw [act_apply, hab, σ_convMul, map_convMul]
  rfl

theorem act_zero
    (hθ_add : ∀ a b : k, toConv (θ (a + b) : H →ₐ[ℤ_[p]] H) =
      toConv (θ a : H →ₐ[ℤ_[p]] H) * toConv (θ b : H →ₐ[ℤ_[p]] H)) (z) :
    act p H θ 0 z = 0 := by
  have h := act_add hθ_add (0 : k) 0 z
  rw [add_zero] at h
  have h2 : act p H θ 0 z + act p H θ 0 z = act p H θ 0 z + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem act_natCast
    (hθ_add : ∀ a b : k, toConv (θ (a + b) : H →ₐ[ℤ_[p]] H) =
      toConv (θ a : H →ₐ[ℤ_[p]] H) * toConv (θ b : H →ₐ[ℤ_[p]] H))
    (hθ_one : θ 1 = BialgHom.id ℤ_[p] H) (m : ℕ) (z) :
    act p H θ (m : k) z = m • z := by
  induction m with
  | zero => rw [Nat.cast_zero, act_zero hθ_add, zero_smul]
  | succ m ih => rw [Nat.cast_succ, act_add hθ_add, ih, act_one hθ_one, succ_nsmul]

theorem p_nsmul_eq_zero [CharP k p]
    (hθ_add : ∀ a b : k, toConv (θ (a + b) : H →ₐ[ℤ_[p]] H) =
      toConv (θ a : H →ₐ[ℤ_[p]] H) * toConv (θ b : H →ₐ[ℤ_[p]] H))
    (hθ_one : θ 1 = BialgHom.id ℤ_[p] H) (z : DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)) :
    p • z = 0 := by
  rw [← act_natCast hθ_add hθ_one p z, CharP.cast_eq_zero, act_zero hθ_add]

@[reducible] noncomputable def moduleK
    (hθ_mul : ∀ a b : k, θ (a * b) = (θ a).comp (θ b)) (hθ_one : θ 1 = BialgHom.id ℤ_[p] H)
    (hθ_add : ∀ a b : k, toConv (θ (a + b) : H →ₐ[ℤ_[p]] H) =
      toConv (θ a : H →ₐ[ℤ_[p]] H) * toConv (θ b : H →ₐ[ℤ_[p]] H)) :
    Module k (DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)) where
  smul a z := act p H θ a z
  one_smul z := act_one hθ_one z
  mul_smul a b z := act_mul hθ_mul a b z
  smul_zero a := map_zero _
  smul_add a x y := map_add _ x y
  add_smul a b z := act_add hθ_add a b z
  zero_smul z := act_zero hθ_add z

theorem moduleK_smul_def
    (hθ_mul : ∀ a b : k, θ (a * b) = (θ a).comp (θ b)) (hθ_one : θ 1 = BialgHom.id ℤ_[p] H)
    (hθ_add : ∀ a b : k, toConv (θ (a + b) : H →ₐ[ℤ_[p]] H) =
      toConv (θ a : H →ₐ[ℤ_[p]] H) * toConv (θ b : H →ₐ[ℤ_[p]] H)) (a : k) (z) :
    (letI := moduleK hθ_mul hθ_one hθ_add; a • z) = DieudonneModule.map (ZMod p) p (σ p H (θ a)) z := rfl

end S17KHonda

open S17KHonda WithConv Deformation in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (hunip : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H)))
    (n : ℕ) (hrank : Module.finrank ℤ_[p] H = Nat.card k ^ n)
    (θ : k → (H →ₐc[ℤ_[p]] H))
    (hθ_mul : ∀ a b : k, θ (a * b) = (θ a).comp (θ b)) (hθ_one : θ 1 = BialgHom.id ℤ_[p] H)
    (hθ_add : ∀ a b : k, WithConv.toConv (θ (a + b) : H →ₐ[ℤ_[p]] H) =
      WithConv.toConv (θ a : H →ₐ[ℤ_[p]] H) * WithConv.toConv (θ b : H →ₐ[ℤ_[p]] H))
    (hθ_zero : WithConv.toConv (θ 0 : H →ₐ[ℤ_[p]] H) = 1) :
    ∃ (D : Type) (_ : AddCommGroup D) (_ : Module k D) (_ : FiniteDimensional k D)
      (𝓗 : Deformation.HondaSystem (0 : k) D)
      (ι : D ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)),
      (∀ x, ι (𝓗.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ι x)) ∧
      (∀ x, ι (𝓗.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ι x)) ∧
      (∀ x, x ∈ 𝓗.L ↔ ι x ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H).toRingHom) ∧
      (∀ (a : k) (x : D), ι (a • x) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θ a)) (ι x)) ∧
      Module.finrank k D = n := by
  classical
  letI instMod : Module k (DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)) := moduleK hθ_mul hθ_one hθ_add
  have smul_def : ∀ (a : k) (z : DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)),
      a • z = DieudonneModule.map (ZMod p) p (σ p H (θ a)) z := fun _ _ => rfl
  have hpz : ∀ z : DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H), (p : ℤ) • z = 0 := by
    intro z
    rw [natCast_zsmul]
    exact p_nsmul_eq_zero hθ_add hθ_one z

  have hsurj : Function.Surjective (algebraMap ℤ_[p] (ZMod p)) := ZMod.ringHom_surjective _
  have hp : ((p : ℕ) : ℤ_[p]) ∈ nonZeroDivisors ℤ_[p] :=
    mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

  haveI := Fintype.ofFinite k
  obtain ⟨f, -, hf⟩ := FiniteField.card k p
  have hk : Nat.card k = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hrank' : ∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a := ⟨(f : ℕ) * n, by rw [hrank, hk, ← pow_mul]⟩
  obtain ⟨Hℤ, hdatum, hL⟩ := DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge p hp hsurj hker H hrank'
  have hFℤ : ∀ z, Hℤ.F z = DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) z := by
    intro z
    rw [show Hℤ.F = Hℤ.toDieudonneDatum.F from rfl, hdatum]
    rfl
  have hVℤ : ∀ z, Hℤ.V z = DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) z := by
    intro z
    rw [show Hℤ.V = Hℤ.toDieudonneDatum.V from rfl, hdatum]
    rfl

  let Fk : DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) →ₗ[k] DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) :=
    { toFun := fun z => DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) z
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a z => by
        rw [RingHom.id_apply, smul_def, smul_def, DieudonneModule.map_frobenius] }
  let Vk : DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) →ₗ[k] DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) :=
    { toFun := fun z => DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) z
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a z => by
        rw [RingHom.id_apply, smul_def, smul_def, DieudonneModule.map_verschiebung] }
  have hFk : ∀ z, Fk z = DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) z := fun _ => rfl
  have hVk : ∀ z, Vk z = DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) z := fun _ => rfl

  let π₀ : H →+* (ZMod p) ⊗[ℤ_[p]] H :=
    (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H).toRingHom
  have hθL : ∀ (a : k) (z : DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)),
      z ∈ fontaineHodge (ZMod p) p π₀ → a • z ∈ fontaineHodge (ZMod p) p π₀ := by
    intro a z hz
    rw [smul_def]
    have hcomm : π₀.comp (θ a : H →ₐ[ℤ_[p]] H).toRingHom =
        ((σ p H (θ a) : _ →ₐc[ZMod p] _) : _ →ₐ[ZMod p] _).toRingHom.comp π₀ := by
      ext h
      rfl
    exact map_fontaineHodge_le π₀ (θ a : H →ₐ[ℤ_[p]] H).toRingHom (σ p H (θ a)) hcomm ⟨z, hz, rfl⟩
  let Lk : Submodule k (DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)) :=
    { carrier := fontaineHodge (ZMod p) p π₀
      add_mem' := fun {x y} hx hy => Submodule.add_mem _ hx hy
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun a z hz => hθL a z hz }
  have hLk : ∀ z, z ∈ Lk ↔ z ∈ fontaineHodge (ZMod p) p π₀ := fun _ => Iff.rfl
  have hLℤ : ∀ z, z ∈ Hℤ.L ↔ z ∈ fontaineHodge (ZMod p) p π₀ := fun z => by rw [hL]

  let 𝓗 : Deformation.HondaSystem (0 : k) (DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)) :=
    { F := Fk
      V := Vk
      fv := by
        apply LinearMap.ext
        intro z
        rw [LinearMap.comp_apply, hFk, hVk, DieudonneModule.frobenius_verschiebung, hpz, zero_smul,
          LinearMap.zero_apply]
      vf := by
        apply LinearMap.ext
        intro z
        rw [LinearMap.comp_apply, hFk, hVk, DieudonneModule.verschiebung_frobenius, hpz, zero_smul,
          LinearMap.zero_apply]
      L := Lk
      sh1_le := by
        intro x hx hxF
        refine ⟨0, Submodule.zero_mem _, ?_⟩
        obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hxF
        have hxL : Fk w ∈ Hℤ.L := (hLℤ _).mpr ((hLk _).mp hx)
        have hxFℤ : Fk w ∈ LinearMap.range Hℤ.F := LinearMap.mem_range.mpr ⟨w, by rw [hFℤ, hFk]⟩
        obtain ⟨y, -, hy⟩ := Hℤ.sh1_le _ hxL hxFℤ
        rw [hy, hpz, zero_smul]
      sh1_ge := by
        intro y _
        rw [zero_smul]
        exact Submodule.zero_mem _
      sh2' := by
        rw [eq_top_iff]
        intro z _
        have hz : z ∈ LinearMap.range Hℤ.F ⊔ Hℤ.L := by rw [Hℤ.sh2']; exact Submodule.mem_top
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
        obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp ha
        refine Submodule.add_mem_sup (LinearMap.mem_range.mpr ⟨w, ?_⟩) ((hLk _).mpr ((hLℤ _).mp hb))
        rw [hFk, hFℤ]
      sh3 := by
        intro x hx hVx
        exact Hℤ.sh3 x ((hLℤ _).mpr ((hLk _).mp hx)) (by rw [hVℤ, ← hVk]; exact hVx) }

  obtain ⟨L, hfinrk, hcard⟩ :=
    DieudonneModule.exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual (ZMod p) p
      ((ZMod p) ⊗[ℤ_[p]] H) hunip
  have hcardM : Nat.card (DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)) = Nat.card k ^ n := by
    rw [hcard, Nat.card_zmod, ← hfinrk, Module.finrank_baseChange, hrank]
  have hk2 : 2 ≤ Nat.card k := by
    rw [hk]
    exact le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow f.ne_zero _)
  haveI : Finite (DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcardM]; exact pow_ne_zero _ (by omega))
  haveI hfin : Module.Finite k (DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)) := Module.Finite.of_finite
  have hdim : Module.finrank k (DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H)) = n := by
    have h := Module.natCard_eq_pow_finrank (K := k) (V := DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H))
    rw [hcardM] at h
    exact (Nat.pow_right_injective hk2 h).symm

  refine ⟨DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H), inferInstance, instMod, hfin, 𝓗,
    AddEquiv.refl _, ?_, ?_, ?_, ?_, hdim⟩
  · intro x; rfl
  · intro x; rfl
  · intro x; exact Iff.rfl
  · intro a x; rfl

end S_Deformation_DieudonneModule_exists_hondaSystem_addEquiv_smul_eq_map_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_hondaSystem_addEquiv_smul_eq_map_of_isLocalRing_cartierDual (solution)
