-- Prove2me | solution 1 for CochainCx.Bounded.exists_contractible_levelwise_equiv_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/65c68a74-df1c-57d6-b621-e152a1b7d2c1

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CochainCx_Bounded_exists_contractible_levelwise_equiv_prod

set_option autoImplicit false

universe u

noncomputable section

namespace CochainCx
p2m_export "CochainCx" "Bounded Bounded.B_zero Bounded.B_succ"
namespace Bounded
p2m_export "CochainCx.Bounded" "B H B_zero B_succ d X N d_sq hBound"
p2m_open "CochainCx.Bounded CochainCx"

namespace Ws48Split

variable {k : Type u} [Field k] (C : CochainCx.Bounded k)

abbrev Z (p : ℕ) : Submodule k (C.X p) := LinearMap.ker (C.d p)

noncomputable def W (p : ℕ) : Submodule k (C.X p) := (Submodule.exists_isCompl (Z C p)).choose

theorem isCompl_Z_W (p : ℕ) : IsCompl (Z C p) (W C p) := (Submodule.exists_isCompl (Z C p)).choose_spec

noncomputable def Hc (p : ℕ) : Submodule k (Z C p) := (Submodule.exists_isCompl (C.B p)).choose

theorem isCompl_B_Hc (p : ℕ) : IsCompl (C.B p) (Hc C p) := (Submodule.exists_isCompl (C.B p)).choose_spec

def Bx (p : ℕ) : Submodule k (C.X p) := (C.B p).map (Z C p).subtype

theorem d_mem_Z (p : ℕ) (x : C.X p) : C.d p x ∈ Z C (p + 1) := by
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, C.d_sq, LinearMap.zero_apply]

theorem d_mem_B (p : ℕ) (x : C.X p) : (⟨C.d p x, d_mem_Z C p x⟩ : Z C (p + 1)) ∈ C.B (p + 1) := by
  rw [CochainCx.Bounded.B_succ, Submodule.mem_comap]
  exact ⟨x, rfl⟩

theorem d_mem_Bx (p : ℕ) (x : C.X p) : C.d p x ∈ Bx C (p + 1) := by
  rw [Bx, Submodule.mem_map]
  exact ⟨⟨C.d p x, d_mem_Z C p x⟩, d_mem_B C p x, rfl⟩

theorem Bx_zero : Bx C 0 = ⊥ := by
  rw [Bx, CochainCx.Bounded.B_zero, Submodule.map_bot]

noncomputable def sZW (p : ℕ) : (Z C p × W C p) ≃ₗ[k] C.X p :=
  Submodule.prodEquivOfIsCompl (Z C p) (W C p) (isCompl_Z_W C p)

noncomputable def sBH (p : ℕ) : (C.B p × Hc C p) ≃ₗ[k] Z C p :=
  Submodule.prodEquivOfIsCompl (C.B p) (Hc C p) (isCompl_B_Hc C p)

noncomputable def qH (p : ℕ) : C.H p ≃ₗ[k] Hc C p :=
  Submodule.quotientEquivOfIsCompl (C.B p) (Hc C p) (isCompl_B_Hc C p)

noncomputable def iB (p : ℕ) : C.B p ≃ₗ[k] Bx C p :=
  Submodule.equivMapOfInjective (Z C p).subtype (Z C p).injective_subtype (C.B p)

theorem iB_coe (p : ℕ) (b : C.B p) : ((iB C p b : Bx C p) : C.X p) = ((b : Z C p) : C.X p) :=
  Submodule.coe_equivMapOfInjective_apply (Z C p).subtype (Z C p).injective_subtype (C.B p) b

theorem decomp (p : ℕ) (x : C.X p) :
    x = (((sZW C p).symm x).1 : C.X p) + (((sZW C p).symm x).2 : C.X p) := by
  conv_lhs => rw [← (sZW C p).apply_symm_apply x]
  exact Submodule.coe_prodEquivOfIsCompl' _ _ _ _

theorem d_eq_d_snd (p : ℕ) (x : C.X p) :
    C.d p x = C.d p (((sZW C p).symm x).2 : C.X p) := by
  conv_lhs => rw [decomp C p x]
  rw [map_add, LinearMap.mem_ker.1 ((sZW C p).symm x).1.2, zero_add]

def dW0 (p : ℕ) : W C p →ₗ[k] Bx C (p + 1) :=
  LinearMap.codRestrict (Bx C (p + 1)) (C.d p ∘ₗ (W C p).subtype) (fun w => d_mem_Bx C p w)

theorem dW0_coe (p : ℕ) (w : W C p) : ((dW0 C p w : Bx C (p + 1)) : C.X (p + 1)) = C.d p w := rfl

theorem dW0_injective (p : ℕ) : Function.Injective (dW0 C p) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  rw [LinearMap.mem_ker] at hw
  have h1 : (w : C.X p) ∈ Z C p := by
    rw [LinearMap.mem_ker, ← dW0_coe, hw]; rfl
  have h2 : (w : C.X p) = 0 := Submodule.disjoint_def.1 (isCompl_Z_W C p).disjoint _ h1 w.2
  exact Subtype.ext h2

theorem dW0_surjective (p : ℕ) : Function.Surjective (dW0 C p) := by
  intro y
  obtain ⟨z, hz, hzy⟩ := (Submodule.mem_map.1 y.2)
  rw [CochainCx.Bounded.B_succ, Submodule.mem_comap, LinearMap.mem_range] at hz
  obtain ⟨x, hx⟩ := hz
  refine ⟨((sZW C p).symm x).2, Subtype.ext ?_⟩
  rw [dW0_coe, ← d_eq_d_snd, hx, ← hzy]

noncomputable def φ (p : ℕ) : W C p ≃ₗ[k] Bx C (p + 1) :=
  LinearEquiv.ofBijective (dW0 C p) ⟨dW0_injective C p, dW0_surjective C p⟩

theorem φ_coe (p : ℕ) (w : W C p) : ((φ C p w : Bx C (p + 1)) : C.X (p + 1)) = C.d p w := rfl

theorem subsingleton_submodule {M : Type u} [AddCommGroup M] [Module k M] [Subsingleton M]
    (S : Submodule k M) : Subsingleton S :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩

noncomputable def E : CochainCx.Bounded k where
  X p := Bx C p × W C p
  d p := LinearMap.inl k (Bx C (p + 1)) (W C (p + 1)) ∘ₗ (φ C p).toLinearMap ∘ₗ
    LinearMap.snd k (Bx C p) (W C p)
  d_sq p := by
    ext x <;> simp
  N := C.N
  hBound n hn := by
    haveI := C.hBound n hn
    haveI := subsingleton_submodule (k := k) (Bx C n)
    haveI := subsingleton_submodule (k := k) (W C n)
    infer_instance

theorem E_d_apply (p : ℕ) (x : Bx C p × W C p) :
    (E C).d p x = ((φ C p x.2 : Bx C (p + 1)), (0 : W C (p + 1))) := rfl

noncomputable def σ (p : ℕ) : (E C).X (p + 1) →ₗ[k] (E C).X p :=
  LinearMap.inr k (Bx C p) (W C p) ∘ₗ (φ C p).symm.toLinearMap ∘ₗ LinearMap.fst k (Bx C (p + 1)) (W C (p + 1))

theorem σ_apply (p : ℕ) (x : Bx C (p + 1) × W C (p + 1)) :
    σ C p x = ((0 : Bx C p), (φ C p).symm x.1) := rfl

theorem σ_d_zero (x : (E C).X 0) : σ C 0 ((E C).d 0 x) = x := by
  obtain ⟨b, w⟩ := x
  rw [E_d_apply, σ_apply]
  refine Prod.ext ?_ ?_
  · have hb : (b : C.X 0) ∈ (⊥ : Submodule k (C.X 0)) := by rw [← Bx_zero C]; exact b.2
    rw [Submodule.mem_bot] at hb
    exact (Subtype.ext hb.symm : (0 : Bx C 0) = b)
  · exact (φ C 0).symm_apply_apply w

theorem σ_d_succ (p : ℕ) (x : (E C).X (p + 1)) :
    σ C (p + 1) ((E C).d (p + 1) x) + (E C).d p (σ C p x) = x := by
  obtain ⟨b, w⟩ := x
  rw [E_d_apply, σ_apply, σ_apply, E_d_apply]
  refine Prod.ext ?_ ?_
  · show (0 : Bx C (p + 1)) + φ C p ((φ C p).symm b) = b
    rw [LinearEquiv.apply_symm_apply, zero_add]
  · show (φ C (p + 1)).symm (φ C (p + 1) w) + 0 = w
    rw [LinearEquiv.symm_apply_apply, add_zero]

noncomputable def e (p : ℕ) : C.X p ≃ₗ[k] (C.H p × (E C).X p) :=
  (sZW C p).symm.trans <|
    (((sBH C p).symm.prodCongr (LinearEquiv.refl k (W C p))).trans <|
      (((LinearEquiv.prodComm k (C.B p) (Hc C p)).prodCongr (LinearEquiv.refl k (W C p))).trans <|
        ((LinearEquiv.prodAssoc k (Hc C p) (C.B p) (W C p)).trans <|
          ((qH C p).symm.prodCongr ((iB C p).prodCongr (LinearEquiv.refl k (W C p)))))))

theorem e_apply (p : ℕ) (x : C.X p) :
    e C p x = ((qH C p).symm ((sBH C p).symm ((sZW C p).symm x).1).2,
      (iB C p ((sBH C p).symm ((sZW C p).symm x).1).1, ((sZW C p).symm x).2)) := rfl

theorem e_d (p : ℕ) (x : C.X p) : e C (p + 1) (C.d p x) = (0, (E C).d p (e C p x).2) := by
  have hyZ := d_mem_Z C p x
  have hyB := d_mem_B C p x
  have h1 : (sZW C (p + 1)).symm (C.d p x) = (⟨C.d p x, hyZ⟩, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left _ _ _ ⟨C.d p x, hyZ⟩
  have h2 : (sBH C (p + 1)).symm ⟨C.d p x, hyZ⟩ = (⟨⟨C.d p x, hyZ⟩, hyB⟩, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left (C.B (p + 1)) (Hc C (p + 1)) (isCompl_B_Hc C (p + 1))
      ⟨⟨C.d p x, hyZ⟩, hyB⟩
  rw [e_apply, h1]
  dsimp only
  rw [h2]
  dsimp only
  rw [map_zero, e_apply]
  dsimp only
  rw [E_d_apply]
  refine Prod.ext rfl (Prod.ext (Subtype.ext ?_) rfl)
  dsimp only
  rw [iB_coe, φ_coe, ← d_eq_d_snd]

end Ws48Split

end CochainCx.Bounded

end

open CochainCx.Bounded.Ws48Split in
theorem solution
    {k : Type u} [Field k] (C : CochainCx.Bounded k) :
    ∃ (E : CochainCx.Bounded k) (σ : ∀ p : ℕ, E.X (p + 1) →ₗ[k] E.X p)
      (_ : ∀ x : E.X 0, σ 0 (E.d 0 x) = x)
      (_ : ∀ (p : ℕ) (x : E.X (p + 1)), σ (p + 1) (E.d (p + 1) x) + E.d p (σ p x) = x)
      (e : ∀ p : ℕ, C.X p ≃ₗ[k] (C.H p × E.X p)),
      ∀ (p : ℕ) (x : C.X p), e (p + 1) (C.d p x) = (0, E.d p (e p x).2) := by
  exact ⟨E C, σ C, σ_d_zero C, σ_d_succ C, e C, e_d C⟩

end S_CochainCx_Bounded_exists_contractible_levelwise_equiv_prod
end P2MW
export P2MW.S_CochainCx_Bounded_exists_contractible_levelwise_equiv_prod (solution)
