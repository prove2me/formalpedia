-- Prove2me | solution 1 for CohCarrier.map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/981548f6-6d7a-5bc1-b100-793459df740b

import Mathlib
import Definitions.Def_CohCarrier_SubfamilyHeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_CohCarrier_surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le
import Theorems.Thm_CohCarrier_jDeg_heckeT_comm_flat
import Theorems.Thm_CohCarrier_jDeg_heckeT_comm_of_dvd
import Theorems.Thm_CohCarrier_jDeg_diamondRaw_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open scoped IsMulCommutative
open CongruenceSubgroup
open scoped MatrixGroups

namespace TWDescentSubSol

open CohCarrier IharaLemma

section Equivariance

variable {L : ℕ} [NeZero L] {S : Set ℕ} {𝒪 : Type} [CommRing 𝒪]
  {H H' : Subgroup (ZMod L)ˣ} (h : LevelLE L L H' H 1)

theorem jDegL_apply (x : H1 L H 𝒪) :
    jDegL L L H' H 1 𝒪 𝒪 h x = jDeg L L H' H 1 𝒪 h x := rfl

theorem diamondRaw_eq_self_of_mem (σ : ↥(Gamma0 L)) (hσ : (σ : SL(2, ℤ)) ∈ GammaH L H')
    (ψ : H1 L H' 𝒪) : diamondRaw L H' 𝒪 σ ψ = ψ := by
  refine AddMonoidHom.ext fun a => ?_
  set γ := Additive.toMul a
  change ψ (Additive.ofMul (conjHom L H' σ γ)) = ψ (Additive.ofMul γ)
  have : conjHom L H' σ γ = ⟨σ, hσ⟩ * γ * ⟨σ, hσ⟩⁻¹ := Subtype.ext rfl
  rw [this, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, add_neg_cancel_comm]

theorem diamondL_eq_self_of_mem {u : (ZMod L)ˣ} (hu : u ∈ H') (ψ : H1 L H' 𝒪) :
    diamondL L H' 𝒪 u ψ = ψ := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective L u
  rw [diamondL_eq_diamondRaw L H' 𝒪 u σ hσ]
  exact diamondRaw_eq_self_of_mem σ (mem_GammaH_iff.mpr ⟨σ.2, by simpa [hσ] using hu⟩) ψ

theorem jDeg_diamondL (u : (ZMod L)ˣ) (x : H1 L H 𝒪) :
    jDeg L L H' H 1 𝒪 h (diamondL L H 𝒪 u x) = diamondL L H' 𝒪 u (jDeg L L H' H 1 𝒪 h x) := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective L u
  rw [diamondL_eq_diamondRaw L H 𝒪 u σ hσ, diamondL_eq_diamondRaw L H' 𝒪 u σ hσ,
    jDeg_diamondRaw_comm σ σ.2 h x]

theorem jDeg_opFamily (g : Gen L S) (x : H1 L H 𝒪) :
    jDeg L L H' H 1 𝒪 h (opFamily L H S 𝒪 g x) = opFamily L H' S 𝒪 g (jDeg L L H' H 1 𝒪 h x) := by
  cases g with
  | T ℓ hℓ hℓS hℓL =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    show jDeg L L H' H 1 𝒪 h (heckeT L H ℓ 𝒪 x) = heckeT L H' ℓ 𝒪 (jDeg L L H' H 1 𝒪 h x)
    exact (jDeg_heckeT_comm_flat h (Nat.coprime_one_right ℓ) hℓ hℓL x).symm
  | U q hq hqL =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    show jDeg L L H' H 1 𝒪 h (heckeT L H q 𝒪 x) = heckeT L H' q 𝒪 (jDeg L L H' H 1 𝒪 h x)
    exact (jDeg_heckeT_comm_of_dvd h hqL x).symm
  | dia d => exact jDeg_diamondL h d x

end Equivariance

section Descent

variable {L : ℕ} [NeZero L] {S : Set ℕ} {𝒪 : Type} [CommRing 𝒪] {k : Type} [Field k]
  [Algebra 𝒪 k] {H H' : Subgroup (ZMod L)ˣ} (h : LevelLE L L H' H 1)
  {G : Type} {fam : G → Gen L S} {dG : ↥H' → G}
  (hdG : ∀ u : ↥H', fam (dG u) = Gen.dia (u : (ZMod L)ˣ))
  {hcomm : ∀ g g' : G,
    opFamily L H S 𝒪 (fam g) * opFamily L H S 𝒪 (fam g') =
      opFamily L H S 𝒪 (fam g') * opFamily L H S 𝒪 (fam g)}
  {hcomm' : ∀ g g' : G,
    opFamily L H' S 𝒪 (fam g) * opFamily L H' S 𝒪 (fam g') =
      opFamily L H' S 𝒪 (fam g') * opFamily L H' S 𝒪 (fam g)}
  {θbar : G → k}

include hdG in

theorem diamondL_mem {u : (ZMod L)ˣ} (hu : u ∈ H') :
    diamondL L H 𝒪 u ∈ (hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra := by
  refine Algebra.subset_adjoin ⟨dG ⟨u, hu⟩, ?_⟩
  show opFamily L H S 𝒪 (fam (dG ⟨u, hu⟩)) = diamondL L H 𝒪 u
  rw [hdG ⟨u, hu⟩]
  rfl

include hdG in

theorem apply_diamondL (b : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) {u : (ZMod L)ˣ}
    (hu : u ∈ H') (x : H1 L H 𝒪) :
    (b : Module.End 𝒪 (H1 L H 𝒪)) (diamondL L H 𝒪 u x) =
      diamondL L H 𝒪 u ((b : Module.End 𝒪 (H1 L H 𝒪)) x) := by
  have hmem : diamondL L H 𝒪 u ∈ (hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra :=
    diamondL_mem hdG hu
  have := mul_comm b ⟨diamondL L H 𝒪 u, hmem⟩
  have := congrArg (fun z : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra =>
    (z : Module.End 𝒪 (H1 L H 𝒪)) x) this
  exact this

variable (hsurj : Function.Surjective (jDeg L L H' H 1 𝒪 h))
  (hker : ∀ x : H1 L H 𝒪, jDeg L L H' H 1 𝒪 h x = 0 ↔
    x ∈ AddSubgroup.closure {y : H1 L H 𝒪 | ∃ σ : ↥(Gamma0 L), (σ : SL(2, ℤ)) ∈ GammaH L H' ∧
      ∃ x : H1 L H 𝒪, y = diamondRaw L H 𝒪 σ x - x})

theorem jDeg_smul_apply (c : 𝒪) (x : H1 L H 𝒪) :
    jDeg L L H' H 1 𝒪 h (c • x) = c • jDeg L L H' H 1 𝒪 h x :=
  map_smul (jDegL L L H' H 1 𝒪 𝒪 h) c x

include hdG hker in

theorem jDeg_apply_eq_zero (b : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) (x : H1 L H 𝒪)
    (hx : jDeg L L H' H 1 𝒪 h x = 0) :
    jDeg L L H' H 1 𝒪 h ((b : Module.End 𝒪 (H1 L H 𝒪)) x) = 0 := by
  rw [hker] at hx ⊢
  refine AddSubgroup.closure_induction (p := fun y _ =>
    (b : Module.End 𝒪 (H1 L H 𝒪)) y ∈ _) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨σ, hσ, x, rfl⟩
    refine AddSubgroup.subset_closure ⟨σ, hσ, (b : Module.End 𝒪 (H1 L H 𝒪)) x, ?_⟩
    have hu : gamma0Units L σ ∈ H' := by
      obtain ⟨h0, hu⟩ := mem_GammaH_iff.mp hσ
      exact hu
    rw [map_sub, ← diamondL_eq_diamondRaw L H 𝒪 (gamma0Units L σ) σ rfl, apply_diamondL hdG b hu,
      diamondL_eq_diamondRaw L H 𝒪 (gamma0Units L σ) σ rfl]
  · show (b : Module.End 𝒪 (H1 L H 𝒪)) 0 ∈ _
    rw [map_zero]; exact zero_mem _
  · intro x y _ _ hx hy
    show (b : Module.End 𝒪 (H1 L H 𝒪)) (x + y) ∈ _
    rw [map_add]; exact add_mem hx hy
  · intro x _ hx
    show (b : Module.End 𝒪 (H1 L H 𝒪)) (-x) ∈ _
    rw [map_neg]; exact neg_mem hx

include hdG hker in
theorem jDeg_apply_congr (b : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) (x y : H1 L H 𝒪)
    (hxy : jDeg L L H' H 1 𝒪 h x = jDeg L L H' H 1 𝒪 h y) :
    jDeg L L H' H 1 𝒪 h ((b : Module.End 𝒪 (H1 L H 𝒪)) x) =
      jDeg L L H' H 1 𝒪 h ((b : Module.End 𝒪 (H1 L H 𝒪)) y) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  apply jDeg_apply_eq_zero h hdG hker
  rw [map_sub, sub_eq_zero, hxy]

def rho (b : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) : Module.End 𝒪 (H1 L H' 𝒪) where
  toFun ψ := jDeg L L H' H 1 𝒪 h ((b : Module.End 𝒪 (H1 L H 𝒪)) (Function.surjInv hsurj ψ))
  map_add' ψ ψ' := by
    rw [← map_add, ← map_add]
    apply jDeg_apply_congr h hdG hker
    rw [map_add, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj]
  map_smul' c ψ := by
    rw [RingHom.id_apply, ← jDeg_smul_apply, ← map_smul (b : Module.End 𝒪 (H1 L H 𝒪))]
    apply jDeg_apply_congr h hdG hker
    rw [jDeg_smul_apply, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj]

theorem rho_apply_jDeg (b : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) (x : H1 L H 𝒪) :
    rho h hdG hsurj hker b (jDeg L L H' H 1 𝒪 h x) =
      jDeg L L H' H 1 𝒪 h ((b : Module.End 𝒪 (H1 L H 𝒪)) x) := by
  show jDeg L L H' H 1 𝒪 h ((b : Module.End 𝒪 (H1 L H 𝒪)) (Function.surjInv hsurj _)) = _
  apply jDeg_apply_congr h hdG hker
  rw [Function.surjInv_eq hsurj]

def rhoA : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra →ₐ[𝒪] Module.End 𝒪 (H1 L H' 𝒪) where
  toFun := rho h hdG hsurj hker
  map_one' := by
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨x, rfl⟩ := hsurj ψ
    rw [rho_apply_jDeg]; rfl
  map_mul' b c := by
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨x, rfl⟩ := hsurj ψ
    rw [Module.End.mul_apply, rho_apply_jDeg, rho_apply_jDeg, rho_apply_jDeg]; rfl
  map_zero' := by
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨x, rfl⟩ := hsurj ψ
    rw [rho_apply_jDeg]
    show jDeg L L H' H 1 𝒪 h 0 = 0
    rw [map_zero]
  map_add' b c := by
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨x, rfl⟩ := hsurj ψ
    rw [LinearMap.add_apply, rho_apply_jDeg, rho_apply_jDeg, rho_apply_jDeg]
    show jDeg L L H' H 1 𝒪 h (_ + _) = _
    rw [map_add]
  commutes' c := by
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨x, rfl⟩ := hsurj ψ
    rw [rho_apply_jDeg, Module.algebraMap_end_apply]
    show jDeg L L H' H 1 𝒪 h ((algebraMap 𝒪 (Module.End 𝒪 (H1 L H 𝒪)) c) x) = _
    rw [Module.algebraMap_end_apply, ← jDegL_apply, map_smul, jDegL_apply]

theorem rhoA_apply_jDeg (b : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) (x : H1 L H 𝒪) :
    rhoA h hdG hsurj hker b (jDeg L L H' H 1 𝒪 h x) =
      jDeg L L H' H 1 𝒪 h ((b : Module.End 𝒪 (H1 L H 𝒪)) x) :=
  rho_apply_jDeg h hdG hsurj hker b x

theorem rhoA_op (g : G) :
    rhoA h hdG hsurj hker ⟨(hdataSub L H S 𝒪 k fam hcomm θbar).op g,
      Algebra.subset_adjoin (Set.mem_range_self g)⟩ = opFamily L H' S 𝒪 (fam g) := by
  refine LinearMap.ext fun ψ => ?_
  obtain ⟨x, rfl⟩ := hsurj ψ
  rw [rhoA_apply_jDeg]
  exact jDeg_opFamily h (fam g) x

theorem rhoA_mem (b : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) :
    rhoA h hdG hsurj hker b ∈ (hdataSub L H' S 𝒪 k fam hcomm' θbar).opSubalgebra := by
  obtain ⟨b, hb⟩ := b
  refine Algebra.adjoin_induction (p := fun x hx => rhoA h hdG hsurj hker ⟨x, hx⟩ ∈
    (hdataSub L H' S 𝒪 k fam hcomm' θbar).opSubalgebra) ?_ ?_ ?_ ?_ hb
  · rintro x ⟨g, rfl⟩
    rw [rhoA_op]
    exact Algebra.subset_adjoin ⟨g, rfl⟩
  · intro c
    have : (⟨algebraMap 𝒪 (Module.End 𝒪 (H1 L H 𝒪)) c, Subalgebra.algebraMap_mem _ c⟩ :
        ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) =
        algebraMap 𝒪 ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra c := rfl
    rw [this, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ c
  · intro x y hx hy hx' hy'
    have : (⟨x + y, add_mem hx hy⟩ : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) =
        ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add]
    exact add_mem hx' hy'
  · intro x y hx hy hx' hy'
    have : (⟨x * y, mul_mem hx hy⟩ : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) =
        ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul]
    exact mul_mem hx' hy'

def rho' : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra →ₐ[𝒪]
    ↥(hdataSub L H' S 𝒪 k fam hcomm' θbar).opSubalgebra :=
  (rhoA h hdG hsurj hker).codRestrict _ (rhoA_mem (hcomm' := hcomm') h hdG hsurj hker)

theorem coe_rho' (b : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) :
    ((rho' (hcomm' := hcomm') h hdG hsurj hker b : ↥(hdataSub L H' S 𝒪 k fam hcomm' θbar).opSubalgebra) :
      Module.End 𝒪 (H1 L H' 𝒪)) = rhoA h hdG hsurj hker b := rfl

theorem jDeg_smul (b : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) (x : H1 L H 𝒪) :
    jDeg L L H' H 1 𝒪 h ((b : Module.End 𝒪 (H1 L H 𝒪)) x) =
      ((rho' (hcomm' := hcomm') h hdG hsurj hker b : ↥(hdataSub L H' S 𝒪 k fam hcomm' θbar).opSubalgebra) :
        Module.End 𝒪 (H1 L H' 𝒪)) (jDeg L L H' H 1 𝒪 h x) := by
  rw [coe_rho', rhoA_apply_jDeg]

theorem rho'_op (g : G) :
    rho' (hcomm' := hcomm') h hdG hsurj hker ⟨(hdataSub L H S 𝒪 k fam hcomm θbar).op g,
      Algebra.subset_adjoin (Set.mem_range_self g)⟩ =
      ⟨(hdataSub L H' S 𝒪 k fam hcomm' θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ :=
  Subtype.ext (rhoA_op h hdG hsurj hker g)

theorem rho'_surjective :
    Function.Surjective (rho' (hcomm := hcomm) (hcomm' := hcomm') (θbar := θbar) h hdG hsurj hker) := by
  rintro ⟨y, hy⟩
  refine Algebra.adjoin_induction (p := fun x hx => ∃ b,
    rho' (hcomm := hcomm) (hcomm' := hcomm') (θbar := θbar) h hdG hsurj hker b =
    (⟨x, hx⟩ : ↥(hdataSub L H' S 𝒪 k fam hcomm' θbar).opSubalgebra)) ?_ ?_ ?_ ?_ hy
  · rintro x ⟨g, rfl⟩
    exact ⟨_, rho'_op h hdG hsurj hker g⟩
  · intro c
    exact ⟨algebraMap 𝒪 ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra c, AlgHom.commutes _ c⟩
  · rintro x y hx hy ⟨b, hb⟩ ⟨c, hc⟩
    exact ⟨b + c, by rw [map_add, hb, hc]; rfl⟩
  · rintro x y hx hy ⟨b, hb⟩ ⟨c, hc⟩
    exact ⟨b * c, by rw [map_mul, hb, hc]; rfl⟩

end Descent

section RingTheory

variable {𝒪 : Type} [CommRing 𝒪] {k : Type} [Field k] [Algebra 𝒪 k]
  {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B] [Algebra 𝒪 B']

def toCornerRingₐ (Sq : IdempotentSplitting B) (i : Fin Sq.n) : B →ₐ[𝒪] Sq.CornerRing i :=
  { Sq.toCornerRing i with commutes' := fun _ => rfl }

@[scoped simp] theorem toCornerRingₐ_apply (Sq : IdempotentSplitting B) (i : Fin Sq.n) (b : B) :
    toCornerRingₐ (𝒪 := 𝒪) Sq i b = Sq.toCornerRing i b := rfl

theorem toCornerRing_e (Sq : IdempotentSplitting B) (i : Fin Sq.n) :
    Sq.toCornerRing i (Sq.e i) = 1 := by
  apply Subtype.ext
  rw [IdempotentSplitting.coe_toCornerRing, (Sq.idem i).eq, (Sq.idem i).eq]
  rfl

theorem 𝔪_eq_ker (hk : Function.Surjective (algebraMap 𝒪 k)) (Sq : IdempotentSplitting B)
    (i : Fin Sq.n) (π : Sq.CornerRing i →ₐ[𝒪] k) :
    Sq.𝔪 i = RingHom.ker ((π.comp (toCornerRingₐ Sq i)).toRingHom) := by
  set χ := (π.comp (toCornerRingₐ (𝒪 := 𝒪) Sq i)).toRingHom with hχ
  have hsurjχ : Function.Surjective χ := by
    intro x
    obtain ⟨c, rfl⟩ := hk x
    exact ⟨algebraMap 𝒪 B c, by rw [hχ]; exact AlgHom.commutes _ c⟩
  haveI hmax : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hsurjχ
  obtain ⟨j, hj⟩ := Sq.exists_eq _ hmax
  by_cases hij : i = j
  · subst hij; exact hj
  · exfalso
    have hmem : Sq.e i ∈ Sq.𝔪 j := (Sq.mem_iff i j).mpr hij
    rw [hj, RingHom.mem_ker, hχ] at hmem
    change π (Sq.toCornerRing i (Sq.e i)) = 0 at hmem
    rw [toCornerRing_e, map_one] at hmem
    exact one_ne_zero hmem

theorem idem_eq_zero_of_mem_maximalIdeal {C : Type} [CommRing C] [IsLocalRing C]
    {u : C} (hu : IsIdempotentElem u) (hmem : u ∈ IsLocalRing.maximalIdeal C) : u = 0 := by
  have h1 : IsUnit (1 - u) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits u ((IsLocalRing.mem_maximalIdeal u).mp hmem)
  have h0 : (1 - u) * u = 0 := by rw [sub_mul, one_mul, hu.eq, sub_self]
  exact (IsUnit.mul_right_eq_zero h1).mp h0

theorem idem_eq_one_of_isUnit {C : Type} [CommRing C] {u : C} (hu : IsIdempotentElem u)
    (h1 : IsUnit u) : u = 1 := by
  have : u * u = u * 1 := by rw [mul_one]; exact hu.eq
  exact h1.mul_left_cancel this

theorem map_e_eq (hk : Function.Surjective (algebraMap 𝒪 k)) (ρ : B →ₐ[𝒪] B')
    (hρ : Function.Surjective ρ)
    (Sq : IdempotentSplitting B) (i : Fin Sq.n) (π : Sq.CornerRing i →ₐ[𝒪] k)
    (Sq' : IdempotentSplitting B') (i' : Fin Sq'.n) (π' : Sq'.CornerRing i' →ₐ[𝒪] k)
    (hχ : (π'.comp (toCornerRingₐ Sq' i')).comp ρ = π.comp (toCornerRingₐ Sq i)) :
    ρ (Sq.e i) = Sq'.e i' := by
  set f := ρ (Sq.e i) with hf
  have hfid : IsIdempotentElem f := (Sq.idem i).map ρ
  have h𝔪 := 𝔪_eq_ker hk Sq i π
  have h𝔪' := 𝔪_eq_ker hk Sq' i' π'

  have ha : f ∉ Sq'.𝔪 i' := by
    rw [h𝔪', RingHom.mem_ker, hf]
    change (((π'.comp (toCornerRingₐ Sq' i')).comp ρ) (Sq.e i)) ≠ 0
    rw [hχ, AlgHom.comp_apply, toCornerRingₐ_apply, toCornerRing_e, map_one]
    exact one_ne_zero

  have hb : ∀ j, j ≠ i' → f ∈ Sq'.𝔪 j := by
    intro j hj
    haveI : (Sq'.𝔪 j).IsMaximal := Sq'.isMaximal j
    haveI hP : ((Sq'.𝔪 j).comap ρ).IsMaximal := Ideal.comap_isMaximal_of_surjective ρ hρ
    obtain ⟨l, hl⟩ := Sq.exists_eq _ hP
    by_cases hli : l = i
    · exfalso
      subst hli

      have h1 : (Sq'.𝔪 j).comap ρ = (Sq'.𝔪 i').comap ρ := by
        rw [← hl, h𝔪, h𝔪', ← hχ]
        rfl
      exact hj (Sq'.𝔪_injective (Ideal.comap_injective_of_surjective ρ hρ h1))
    · have : Sq.e i ∈ Sq.𝔪 l := (Sq.mem_iff i l).mpr (Ne.symm hli)
      rw [hl, Ideal.mem_comap] at this
      exact this

  have hc : ∀ j, j ≠ i' → Sq'.e j * f = 0 := by
    intro j hj
    have hu : algebraMap B' (Sq'.CornerRing j) f ∈ IsLocalRing.maximalIdeal (Sq'.CornerRing j) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Sq'.CornerRing j) (Sq'.𝔪 j) f).mpr (hb j hj)
    have h0 := idem_eq_zero_of_mem_maximalIdeal (hfid.map (algebraMap B' (Sq'.CornerRing j))) hu
    have h0' : Sq'.e j * f * Sq'.e j = 0 := congrArg Subtype.val h0
    rwa [mul_comm (Sq'.e j) f, mul_assoc, (Sq'.idem j).eq, mul_comm] at h0'

  have hd : Sq'.e i' * f = Sq'.e i' := by
    have hu : IsUnit (algebraMap B' (Sq'.CornerRing i') f) :=
      IsLocalization.map_units (Sq'.CornerRing i') (⟨f, ha⟩ : (Sq'.𝔪 i').primeCompl)
    have h1 := idem_eq_one_of_isUnit (hfid.map (algebraMap B' (Sq'.CornerRing i'))) hu
    have h1' : Sq'.e i' * f * Sq'.e i' = Sq'.e i' := congrArg Subtype.val h1
    rwa [mul_comm (Sq'.e i') f, mul_assoc, (Sq'.idem i').eq, mul_comm] at h1'

  calc f = f * ∑ j, Sq'.e j := by rw [Sq'.coi.complete, mul_one]
    _ = ∑ j, Sq'.e j * f := by rw [Finset.mul_sum]; simp_rw [mul_comm]
    _ = Sq'.e i' * f := Finset.sum_eq_single i' (fun j _ hj => hc j hj) (fun h => absurd (Finset.mem_univ _) h)
    _ = Sq'.e i' := hd

end RingTheory

section CornerMap

variable {𝒪 : Type} [CommRing 𝒪] {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B]
  [Algebra 𝒪 B'] (ρ : B →ₐ[𝒪] B') (Sq : IdempotentSplitting B) (i : Fin Sq.n)
  (Sq' : IdempotentSplitting B') (i' : Fin Sq'.n) (he : ρ (Sq.e i) = Sq'.e i')

def cornerMap : Sq.CornerRing i →ₐ[𝒪] Sq'.CornerRing i' where
  toFun z := ⟨ρ (z : B), by
    obtain ⟨a, ha⟩ := z.2
    refine ⟨ρ a, ?_⟩
    show Sq'.e i' * ρ a * Sq'.e i' = ρ z
    rw [← he, ← map_mul, ← map_mul]
    exact congrArg ρ ha⟩
  map_one' := Subtype.ext (by
    show ρ (Sq.e i) = Sq'.e i'
    exact he)
  map_mul' z w := Subtype.ext (by
    show ρ ((z : B) * (w : B)) = ρ z * ρ w
    rw [map_mul])
  map_zero' := Subtype.ext (by
    show ρ 0 = 0
    rw [map_zero])
  map_add' z w := Subtype.ext (by
    show ρ ((z : B) + (w : B)) = ρ z + ρ w
    rw [map_add])
  commutes' c := Subtype.ext (by
    show ρ (Sq.e i * algebraMap 𝒪 B c * Sq.e i) = Sq'.e i' * algebraMap 𝒪 B' c * Sq'.e i'
    rw [map_mul, map_mul, he, AlgHom.commutes])

@[scoped simp] theorem coe_cornerMap (z : Sq.CornerRing i) :
    ((cornerMap ρ Sq i Sq' i' he z : Sq'.CornerRing i') : B') = ρ z := rfl

theorem cornerMap_toCornerRing (b : B) :
    cornerMap ρ Sq i Sq' i' he (Sq.toCornerRing i b) = Sq'.toCornerRing i' (ρ b) := by
  apply Subtype.ext
  rw [coe_cornerMap, IdempotentSplitting.coe_toCornerRing, IdempotentSplitting.coe_toCornerRing,
    map_mul, map_mul, he]

theorem cornerMap_surjective (hρ : Function.Surjective ρ) :
    Function.Surjective (cornerMap ρ Sq i Sq' i' he) := by
  intro w
  obtain ⟨a', ha'⟩ := w.2
  obtain ⟨a, rfl⟩ := hρ a'
  refine ⟨Sq.toCornerRing i a, ?_⟩
  rw [cornerMap_toCornerRing]
  exact Subtype.ext ha'

end CornerMap

section Assembly

variable {L : ℕ} [NeZero L] {S : Set ℕ} {𝒪 : Type} [CommRing 𝒪] {k : Type} [Field k]
  [Algebra 𝒪 k] {H H' : Subgroup (ZMod L)ˣ} (h : LevelLE L L H' H 1)
  {G : Type} {fam : G → Gen L S} {dG : ↥H' → G}
  (hdG : ∀ u : ↥H', fam (dG u) = Gen.dia (u : (ZMod L)ˣ))
  {hcomm : ∀ g g' : G,
    opFamily L H S 𝒪 (fam g) * opFamily L H S 𝒪 (fam g') =
      opFamily L H S 𝒪 (fam g') * opFamily L H S 𝒪 (fam g)}
  {hcomm' : ∀ g g' : G,
    opFamily L H' S 𝒪 (fam g) * opFamily L H' S 𝒪 (fam g') =
      opFamily L H' S 𝒪 (fam g') * opFamily L H' S 𝒪 (fam g)}
  {θbar : G → k}
  (hsurj : Function.Surjective (jDeg L L H' H 1 𝒪 h))
  (hker : ∀ x : H1 L H 𝒪, jDeg L L H' H 1 𝒪 h x = 0 ↔
    x ∈ AddSubgroup.closure {y : H1 L H 𝒪 | ∃ σ : ↥(Gamma0 L), (σ : SL(2, ℤ)) ∈ GammaH L H' ∧
      ∃ x : H1 L H 𝒪, y = diamondRaw L H 𝒪 σ x - x})
  (Sp : IdempotentSplitting ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] k)
  (hπk : ∀ g : G, πk (Sp.toCornerRing i₀
    ⟨(hdataSub L H S 𝒪 k fam hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
  (Sp' : IdempotentSplitting ↥(hdataSub L H' S 𝒪 k fam hcomm' θbar).opSubalgebra)
  (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] k)
  (hπk' : ∀ g : G, πk' (Sp'.toCornerRing i₀'
    ⟨(hdataSub L H' S 𝒪 k fam hcomm' θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)

include hπk hπk' in

theorem char_compat :
    ((πk'.comp (toCornerRingₐ Sp' i₀')).comp
        (rho' (hcomm := hcomm) (hcomm' := hcomm') (θbar := θbar) h hdG hsurj hker)) =
      πk.comp (toCornerRingₐ Sp i₀) := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨b, hb⟩ := b
  refine Algebra.adjoin_induction (p := fun x hx =>
    ((πk'.comp (toCornerRingₐ Sp' i₀')).comp
        (rho' (hcomm := hcomm) (hcomm' := hcomm') (θbar := θbar) h hdG hsurj hker)) ⟨x, hx⟩ =
      (πk.comp (toCornerRingₐ Sp i₀)) ⟨x, hx⟩) ?_ ?_ ?_ ?_ hb
  · rintro x ⟨g, rfl⟩
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, toCornerRingₐ_apply,
      toCornerRingₐ_apply]
    erw [rho'_op h hdG hsurj hker g, hπk g, hπk' g]
  · intro c
    have : (⟨algebraMap 𝒪 (Module.End 𝒪 (H1 L H 𝒪)) c, Subalgebra.algebraMap_mem _ c⟩ :
        ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) =
        algebraMap 𝒪 ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra c := rfl
    rw [this, AlgHom.commutes, AlgHom.commutes]
  · intro x y hx hy hx' hy'
    have : (⟨x + y, add_mem hx hy⟩ : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) =
        ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, map_add, hx', hy']
  · intro x y hx hy hx' hy'
    have : (⟨x * y, mul_mem hx hy⟩ : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) =
        ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul, map_mul, hx', hy']

include hker in

theorem part1 (he : rho' (hcomm := hcomm) (hcomm' := hcomm') (θbar := θbar) h hdG hsurj hker (Sp.e i₀) =
    Sp'.e i₀') :
    Submodule.map (jDegL L L H' H 1 𝒪 𝒪 h)
        ((cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀)).restrictScalars 𝒪) =
      (cornerSubmodule (M := H1 L H' 𝒪) (Sp'.e i₀')).restrictScalars 𝒪 := by
  have hse : ∀ x : H1 L H 𝒪, jDeg L L H' H 1 𝒪 h ((Sp.e i₀ : Module.End 𝒪 (H1 L H 𝒪)) x) =
      (Sp'.e i₀' : Module.End 𝒪 (H1 L H' 𝒪)) (jDeg L L H' H 1 𝒪 h x) := fun x => by
    rw [jDeg_smul (hcomm := hcomm) (hcomm' := hcomm') (θbar := θbar) h hdG hsurj hker (Sp.e i₀) x, he]
  apply le_antisymm
  · rintro y ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, Submodule.restrictScalars_mem, cornerSubmodule, LinearMap.mem_range] at hm
    obtain ⟨m₀, rfl⟩ := hm
    rw [Submodule.restrictScalars_mem, cornerSubmodule, LinearMap.mem_range]
    refine ⟨jDegL L L H' H 1 𝒪 𝒪 h m₀, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.id_apply]
    change (Sp'.e i₀' : Module.End 𝒪 (H1 L H' 𝒪)) (jDeg L L H' H 1 𝒪 h m₀) =
      jDeg L L H' H 1 𝒪 h ((Sp.e i₀ : Module.End 𝒪 (H1 L H 𝒪)) m₀)
    rw [hse]
  · intro y hy
    rw [Submodule.restrictScalars_mem, cornerSubmodule, LinearMap.mem_range] at hy
    obtain ⟨y₀, rfl⟩ := hy
    obtain ⟨m₀, hm₀⟩ := hsurj y₀
    refine ⟨(Sp.e i₀ : Module.End 𝒪 (H1 L H 𝒪)) m₀, ?_, ?_⟩
    · rw [SetLike.mem_coe, Submodule.restrictScalars_mem, cornerSubmodule, LinearMap.mem_range]
      exact ⟨m₀, rfl⟩
    · rw [LinearMap.smul_apply, LinearMap.id_apply]
      change jDeg L L H' H 1 𝒪 h ((Sp.e i₀ : Module.End 𝒪 (H1 L H 𝒪)) m₀) =
        (Sp'.e i₀' : Module.End 𝒪 (H1 L H' 𝒪)) y₀
      rw [hse, hm₀]

include hdG hker in

theorem part2 (m : H1 L H 𝒪) (hm : m ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀)) :
    jDegL L L H' H 1 𝒪 𝒪 h m = 0 ↔
      m ∈ Submodule.span 𝒪 {y : H1 L H 𝒪 | ∃ u ∈ H',
        ∃ x ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀), y = diamondL L H 𝒪 u x - x} := by
  have hem : (Sp.e i₀ : Module.End 𝒪 (H1 L H 𝒪)) m = m := by
    rw [cornerSubmodule, LinearMap.mem_range] at hm
    obtain ⟨m₀, rfl⟩ := hm
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    change (Sp.e i₀ * Sp.e i₀ : ↥(hdataSub L H S 𝒪 _ fam hcomm θbar).opSubalgebra) • m₀ = Sp.e i₀ • m₀
    rw [(Sp.idem i₀).eq]
  constructor
  · intro h0
    have h0' : jDeg L L H' H 1 𝒪 h m = 0 := h0
    rw [hker] at h0'
    rw [← hem]
    refine AddSubgroup.closure_induction (p := fun y _ =>
      (Sp.e i₀ : Module.End 𝒪 (H1 L H 𝒪)) y ∈ Submodule.span 𝒪 {y : H1 L H 𝒪 | ∃ u ∈ H',
        ∃ x ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀), y = diamondL L H 𝒪 u x - x})
      ?_ ?_ ?_ ?_ h0'
    · rintro y ⟨σ, hσ, x, rfl⟩
      have hu : gamma0Units L σ ∈ H' := by
        obtain ⟨h0, hu⟩ := mem_GammaH_iff.mp hσ
        exact hu
      refine Submodule.subset_span ⟨gamma0Units L σ, hu,
        (Sp.e i₀ : Module.End 𝒪 (H1 L H 𝒪)) x, ?_, ?_⟩
      · rw [cornerSubmodule, LinearMap.mem_range]
        exact ⟨x, rfl⟩
      · rw [map_sub, ← diamondL_eq_diamondRaw L H 𝒪 (gamma0Units L σ) σ rfl, apply_diamondL hdG _ hu]
    · change (Sp.e i₀ : Module.End 𝒪 (H1 L H 𝒪)) 0 ∈ _
      rw [map_zero]; exact zero_mem _
    · intro x y _ _ hx hy
      change (Sp.e i₀ : Module.End 𝒪 (H1 L H 𝒪)) (x + y) ∈ _
      rw [map_add]; exact add_mem hx hy
    · intro x _ hx
      change (Sp.e i₀ : Module.End 𝒪 (H1 L H 𝒪)) (-x) ∈ _
      rw [map_neg]; exact neg_mem hx
  · intro hspan
    have : Submodule.span 𝒪 {y : H1 L H 𝒪 | ∃ u ∈ H',
        ∃ x ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀), y = diamondL L H 𝒪 u x - x} ≤
        LinearMap.ker (jDegL L L H' H 1 𝒪 𝒪 h) := by
      rw [Submodule.span_le]
      rintro y ⟨u, hu, x, _, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, jDegL_apply, jDegL_apply, jDeg_diamondL,
        diamondL_eq_self_of_mem hu, sub_self]
    exact this hspan

include hker in

theorem part3 (he : rho' (hcomm := hcomm) (hcomm' := hcomm') (θbar := θbar) h hdG hsurj hker (Sp.e i₀) =
    Sp'.e i₀') :
    ∃ Φ : Sp.CornerRing i₀ →ₐ[𝒪] Sp'.CornerRing i₀',
      Function.Surjective Φ ∧
      (∀ g : G,
        Φ (Sp.toCornerRing i₀
            ⟨(hdataSub L H S 𝒪 k fam hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) =
          Sp'.toCornerRing i₀'
            ⟨(hdataSub L H' S 𝒪 k fam hcomm' θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) ∧
      (∀ (z : Sp.CornerRing i₀) (m : H1 L H 𝒪),
        m ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀) →
          jDegL L L H' H 1 𝒪 𝒪 h ((z : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) • m) =
            ((Φ z : Sp'.CornerRing i₀') : ↥(hdataSub L H' S 𝒪 k fam hcomm' θbar).opSubalgebra) •
              jDegL L L H' H 1 𝒪 𝒪 h m) := by
  refine ⟨cornerMap _ Sp i₀ Sp' i₀' he,
    cornerMap_surjective _ Sp i₀ Sp' i₀' he (rho'_surjective h hdG hsurj hker), fun g => ?_,
    fun z m _ => ?_⟩
  · rw [cornerMap_toCornerRing, rho'_op]
  · exact jDeg_smul (hcomm' := hcomm') (θbar := θbar) h hdG hsurj hker
      (z : ↥(hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra) m

end Assembly

end TWDescentSubSol
p2m_reactivate "P2MW.S_CohCarrier_map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily.TWDescentSubSol"

open TWDescentSubSol CohCarrier IharaLemma in
theorem solution
    (L : ℕ) [NeZero L] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (H H' : Subgroup (ZMod L)ˣ) (h : CohCarrier.LevelLE L L H' H 1)
    (r : ℕ) (hrL : r ∣ L) (hr : 4 ≤ r)
    (hH' : ∀ u ∈ H', ZMod.castHom hrL (ZMod r) (u : ZMod L) = 1)

    {G : Type} (φ : G → CohCarrier.Gen L S)
    (dG : ↥H' → G) (hdG : ∀ u : ↥H', φ (dG u) = CohCarrier.Gen.dia (u : (ZMod L)ˣ))
    (hcomm : ∀ g g' : G,
      CohCarrier.opFamily L H S 𝒪 (φ g) * CohCarrier.opFamily L H S 𝒪 (φ g') =
        CohCarrier.opFamily L H S 𝒪 (φ g') * CohCarrier.opFamily L H S 𝒪 (φ g))
    (hcomm' : ∀ g g' : G,
      CohCarrier.opFamily L H' S 𝒪 (φ g) * CohCarrier.opFamily L H' S 𝒪 (φ g') =
        CohCarrier.opFamily L H' S 𝒪 (φ g') * CohCarrier.opFamily L H' S 𝒪 (φ g))
    (θbar : G → IsLocalRing.ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : G, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (Sp' : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).opSubalgebra)
    (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk' : ∀ g : G, πk' (Sp'.toCornerRing i₀'
      ⟨(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g) :

    Submodule.map (CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h)
        ((IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)).restrictScalars 𝒪) =
      (IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀')).restrictScalars 𝒪 ∧

    (∀ m : CohCarrier.H1 L H 𝒪,
      m ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀) →
        (CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h m = 0 ↔
          m ∈ Submodule.span 𝒪 {y : CohCarrier.H1 L H 𝒪 | ∃ u ∈ H',
            ∃ x ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀),
              y = CohCarrier.diamondL L H 𝒪 u x - x})) ∧

    ∃ Φ : Sp.CornerRing i₀ →ₐ[𝒪] Sp'.CornerRing i₀',
      Function.Surjective Φ ∧
      (∀ g : G,
        Φ (Sp.toCornerRing i₀
            ⟨(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).op g,
              Algebra.subset_adjoin (Set.mem_range_self g)⟩) =
          Sp'.toCornerRing i₀'
            ⟨(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).op g,
              Algebra.subset_adjoin (Set.mem_range_self g)⟩) ∧
      (∀ (z : Sp.CornerRing i₀) (m : CohCarrier.H1 L H 𝒪),
        m ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀) →
          CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h
              ((z : ↥(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).opSubalgebra)
                • m) =
            ((Φ z : Sp'.CornerRing i₀') :
                ↥(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).opSubalgebra)
              • CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h m) := by

  obtain ⟨hsurj, hker⟩ :=
    CohCarrier.surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le L 𝒪 H H' h r hrL hr hH'
  have hk : Function.Surjective (algebraMap 𝒪 (IsLocalRing.ResidueField 𝒪)) :=
    IsLocalRing.residue_surjective

  have he : rho' (hcomm := hcomm) (hcomm' := hcomm') (θbar := θbar) h hdG hsurj hker (Sp.e i₀) =
      Sp'.e i₀' :=
    map_e_eq hk _ (rho'_surjective h hdG hsurj hker) Sp i₀ πk Sp' i₀' πk'
      (char_compat h hdG hsurj hker Sp i₀ πk hπk Sp' i₀' πk' hπk')
  exact ⟨part1 h hdG hsurj hker Sp i₀ Sp' i₀' he, part2 h hdG hker Sp i₀,
    part3 h hdG hsurj hker Sp i₀ Sp' i₀' he⟩

end
end S_CohCarrier_map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily
end P2MW
export P2MW.S_CohCarrier_map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily (solution)
