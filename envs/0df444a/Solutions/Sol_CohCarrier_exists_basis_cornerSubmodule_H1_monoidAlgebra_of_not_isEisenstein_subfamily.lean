-- Prove2me | solution 1 for CohCarrier.exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0f049a9d-ceb2-592d-a9be-68a26f3c1553

import Mathlib
import Definitions.Def_CohCarrier_SubfamilyHeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_CohCarrier_map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily
import Theorems.Thm_CohCarrier_finrank_cornerSubmodule_H1_eq_relIndex_mul_of_not_isEisenstein_subfamily
import Theorems.Thm_TW12_exists_groupAlgebra_basis_of_descent
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace U5FreeSubSol

open CohCarrier IharaLemma
open scoped IsMulCommutative

section Augmentation

variable {𝒪 : Type} [CommRing 𝒪] {Δ : Type} [CommGroup Δ]
  {M : Type} [AddCommGroup M] [Module (MonoidAlgebra 𝒪 Δ) M] [Module 𝒪 M]
  [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 Δ) M]

theorem mem_aug_iff (a : MonoidAlgebra 𝒪 Δ) :
    a ∈ RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) ↔
      Coalgebra.counit (R := 𝒪) a = 0 := by
  simp [RingHom.mem_ker]

theorem of_sub_one_mem_aug (δ : Δ) :
    MonoidAlgebra.of 𝒪 Δ δ - 1 ∈ RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) := by
  rw [mem_aug_iff, map_sub, MonoidAlgebra.of_apply, MonoidAlgebra.counit_single,
    MonoidAlgebra.one_def, MonoidAlgebra.counit_single, sub_self]

theorem single_smul_eq (δ : Δ) (a : 𝒪) (m : M) :
    (MonoidAlgebra.single δ a : MonoidAlgebra 𝒪 Δ) • m = a • ((MonoidAlgebra.of 𝒪 Δ δ) • m) := by
  have : (MonoidAlgebra.single δ a : MonoidAlgebra 𝒪 Δ) = a • MonoidAlgebra.of 𝒪 Δ δ := by
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rw [this, smul_assoc]

theorem smul_sub_counit_smul_mem_span (a : MonoidAlgebra 𝒪 Δ) (m : M) :
    a • m - (Coalgebra.counit (R := 𝒪) a) • m ∈
      Submodule.span 𝒪 {z : M | ∃ (δ : Δ) (x : M), z = (MonoidAlgebra.of 𝒪 Δ δ) • x - x} := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => rw [zero_smul, map_zero, zero_smul, sub_zero]; exact Submodule.zero_mem _
  | add x y hx hy =>
    have : (x + y) • m - (Coalgebra.counit (R := 𝒪) (x + y)) • m =
        (x • m - (Coalgebra.counit (R := 𝒪) x) • m) + (y • m - (Coalgebra.counit (R := 𝒪) y) • m) := by
      rw [add_smul, map_add, add_smul]; abel
    rw [this]
    exact Submodule.add_mem _ hx hy
  | single δ a =>
    rw [single_smul_eq, MonoidAlgebra.counit_single, CommSemiring.counit_apply, ← smul_sub]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨δ, m, rfl⟩)

theorem mem_augSmul_iff (m : M) :
    m ∈ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M)) ↔
      m ∈ Submodule.span 𝒪 {z : M | ∃ (δ : Δ) (x : M), z = (MonoidAlgebra.of 𝒪 Δ δ) • x - x} := by
  constructor
  · intro hm
    refine Submodule.smul_induction_on hm (fun a ha n _ => ?_) (fun x y hx hy => Submodule.add_mem _ hx hy)
    have h := smul_sub_counit_smul_mem_span a n
    rwa [(mem_aug_iff a).1 ha, zero_smul, sub_zero] at h
  · intro hm
    have hle : Submodule.span 𝒪 {z : M | ∃ (δ : Δ) (x : M), z = (MonoidAlgebra.of 𝒪 Δ δ) • x - x} ≤
        ((RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ))) •
          (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M)).restrictScalars 𝒪 := by
      rw [Submodule.span_le]
      rintro _ ⟨δ, x, rfl⟩
      have : (MonoidAlgebra.of 𝒪 Δ δ) • x - x = (MonoidAlgebra.of 𝒪 Δ δ - 1) • x := by
        rw [sub_smul, one_smul]
      rw [SetLike.mem_coe, Submodule.restrictScalars_mem, this]
      exact Submodule.smul_mem_smul (of_sub_one_mem_aug δ) Submodule.mem_top
    exact hle hm

end Augmentation

section Group

variable {L : ℕ} [NeZero L] (H H' : Subgroup (ZMod L)ˣ)
  {Δ : Type} [CommGroup Δ] (π : (ZMod L)ˣ →* Δ)

def πH' : ↥H' →* Δ := π.comp H'.subtype

theorem πH'_surjective (hπ : ∀ δ : Δ, ∃ u ∈ H', π u = δ) : Function.Surjective (πH' H' π) := fun δ => by
  obtain ⟨u, hu, rfl⟩ := hπ δ
  exact ⟨⟨u, hu⟩, rfl⟩

theorem ker_πH' (hπH : ∀ u ∈ H', (π u = 1 ↔ u ∈ H)) : (πH' H' π).ker = H.subgroupOf H' := by
  ext ⟨u, hu⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact hπH u hu

theorem finite_Δ (hπ : ∀ δ : Δ, ∃ u ∈ H', π u = δ) : Finite Δ := by
  haveI : Finite (ZMod L)ˣ := inferInstance
  exact Finite.of_surjective _ (πH'_surjective H' π hπ)

theorem natCard_Δ (hπ : ∀ δ : Δ, ∃ u ∈ H', π u = δ) (hπH : ∀ u ∈ H', (π u = 1 ↔ u ∈ H)) :
    Nat.card Δ = H.relIndex H' := by
  rw [Subgroup.relIndex, ← ker_πH' H H' π hπH, Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (πH' H' π)
      (πH'_surjective H' π hπ)).toEquiv]

end Group

section Corner

variable (L : ℕ) [NeZero L] (S : Set ℕ) (H : Subgroup (ZMod L)ˣ)
  (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
  {G : Type} (fam : G → Gen L S)
  (hcomm : ∀ g g' : G,
      opFamily L H S 𝒪 (fam g) * opFamily L H S 𝒪 (fam g') = opFamily L H S 𝒪 (fam g') * opFamily L H S 𝒪 (fam g))
  (θbar : G → k)

local notation3 "𝕋" => (CohCarrier.hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra

def gOp (g : G) : ↥𝕋 :=
  ⟨(hdataSub L H S 𝒪 k fam hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩

theorem subalg_smul_def (b : ↥𝕋) (m : H1 L H 𝒪) :
    b • m = (b : Module.End 𝒪 (H1 L H 𝒪)) m := rfl

theorem gOp_smul (g : G) (m : H1 L H 𝒪) :
    (gOp L S H 𝒪 k fam hcomm θbar g : ↥𝕋) • m = opFamily L H S 𝒪 (fam g) m := rfl

theorem dia_smul {g : G} {u : (ZMod L)ˣ} (hg : fam g = Gen.dia u) (m : H1 L H 𝒪) :
    (gOp L S H 𝒪 k fam hcomm θbar g : ↥𝕋) • m = diamondL L H 𝒪 u m := by
  rw [gOp_smul, hg]
  rfl

theorem algebraMap_subalg_smul (a : 𝒪) (m : H1 L H 𝒪) : (algebraMap 𝒪 ↥𝕋 a) • m = a • m := by
  rw [subalg_smul_def, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply]

variable (Sp : IdempotentSplitting ↥(CohCarrier.hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n)

abbrev Pcs : Submodule 𝒪 (H1 L H 𝒪) :=
  (IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀)).restrictScalars 𝒪

abbrev Pc : Type := ↥(Pcs L S H 𝒪 k fam hcomm θbar Sp i₀)

local notation3 "PP" => Pc L S H 𝒪 k fam hcomm θbar Sp i₀

theorem mem_corner (m : PP) :
    (m : H1 L H 𝒪) ∈ IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀) := m.2

theorem e_smul_of_mem {x : H1 L H 𝒪}
    (hx : x ∈ IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀)) : Sp.e i₀ • x = x :=
  Sp.e_smul_coe i₀ ⟨x, hx⟩

theorem coe_cornerRing_smul_of_mem (b : ↥𝕋) {x : H1 L H 𝒪}
    (hx : x ∈ IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀)) :
    ((Sp.toCornerRing i₀ b : Sp.CornerRing i₀) : ↥𝕋) • x = b • x := by
  rw [IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul, e_smul_of_mem _ _ _ _ _ _ _ _ _ _ hx,
    ← mul_smul, mul_comm, mul_smul, e_smul_of_mem _ _ _ _ _ _ _ _ _ _ hx]

def incl : PP →ₗ[𝒪] H1 L H 𝒪 where
  toFun m := (m : H1 L H 𝒪)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem incl_apply (m : PP) : incl L S H 𝒪 k fam hcomm θbar Sp i₀ m = (m : H1 L H 𝒪) := rfl

theorem incl_injective : Function.Injective (incl L S H 𝒪 k fam hcomm θbar Sp i₀) :=
  fun _ _ hxy => Subtype.ext hxy

def actP : Sp.CornerRing i₀ →+* Module.End 𝒪 PP where
  toFun z :=
    { toFun := fun m => ⟨((z : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) m,
        Sp.coe_smul_mem i₀ z
          (⟨(m : H1 L H 𝒪), mem_corner L S H 𝒪 k fam hcomm θbar Sp i₀ m⟩ :
            ↥(IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀)))⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun r m => Subtype.ext (LinearMap.map_smul _ r _) }
  map_one' := LinearMap.ext fun m => Subtype.ext (by
    show ((1 : Sp.CornerRing i₀) : ↥𝕋) • (m : H1 L H 𝒪) = m
    rw [IdempotentSplitting.coe_one_cornerRing]
    exact e_smul_of_mem L S H 𝒪 k fam hcomm θbar Sp i₀ (mem_corner L S H 𝒪 k fam hcomm θbar Sp i₀ m))
  map_mul' z w := LinearMap.ext fun m => Subtype.ext (by
    show ((z * w : Sp.CornerRing i₀) : ↥𝕋) • (m : H1 L H 𝒪) =
      (z : ↥𝕋) • ((w : ↥𝕋) • (m : H1 L H 𝒪))
    rw [← mul_smul]
    rfl)
  map_zero' := LinearMap.ext fun m => Subtype.ext (by
    show ((0 : Sp.CornerRing i₀) : ↥𝕋) • (m : H1 L H 𝒪) = 0
    rw [IdempotentSplitting.coe_zero_cornerRing, zero_smul])
  map_add' z w := LinearMap.ext fun m => Subtype.ext (by
    show ((z + w : Sp.CornerRing i₀) : ↥𝕋) • (m : H1 L H 𝒪) =
      (z : ↥𝕋) • (m : H1 L H 𝒪) + (w : ↥𝕋) • (m : H1 L H 𝒪)
    rw [← add_smul]
    rfl)

theorem coe_actP_apply (z : Sp.CornerRing i₀) (m : PP) :
    ((actP L S H 𝒪 k fam hcomm θbar Sp i₀ z m : PP) : H1 L H 𝒪) = (z : ↥𝕋) • (m : H1 L H 𝒪) := rfl

theorem actP_algebraMap (a : 𝒪) (m : PP) :
    actP L S H 𝒪 k fam hcomm θbar Sp i₀ (algebraMap 𝒪 (Sp.CornerRing i₀) a) m = a • m := by
  apply Subtype.ext
  rw [coe_actP_apply, Submodule.coe_smul]
  show ((Sp.toCornerRing i₀ (algebraMap 𝒪 ↥𝕋 a) : Sp.CornerRing i₀) : ↥𝕋) • (m : H1 L H 𝒪) = a • (m : H1 L H 𝒪)
  rw [coe_cornerRing_smul_of_mem L S H 𝒪 k fam hcomm θbar Sp i₀ _ (mem_corner L S H 𝒪 k fam hcomm θbar Sp i₀ m),
    algebraMap_subalg_smul]

variable {Δ : Type} [CommGroup Δ] (ι : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] Sp.CornerRing i₀)

@[reducible] def moduleΛ : Module (MonoidAlgebra 𝒪 Δ) PP :=
  Module.compHom PP ((actP L S H 𝒪 k fam hcomm θbar Sp i₀).comp ι.toRingHom)

theorem Λsmul_def (c : MonoidAlgebra 𝒪 Δ) (m : PP) :
    (letI := moduleΛ L S H 𝒪 k fam hcomm θbar Sp i₀ ι; c • m) = actP L S H 𝒪 k fam hcomm θbar Sp i₀ (ι c) m :=
  rfl

theorem coe_Λsmul (c : MonoidAlgebra 𝒪 Δ) (m : PP) :
    (((letI := moduleΛ L S H 𝒪 k fam hcomm θbar Sp i₀ ι; c • m) : PP) : H1 L H 𝒪) =
      ((ι c : Sp.CornerRing i₀) : ↥𝕋) • (m : H1 L H 𝒪) :=
  rfl

theorem isScalarTower_Λ :
    letI := moduleΛ L S H 𝒪 k fam hcomm θbar Sp i₀ ι
    IsScalarTower 𝒪 (MonoidAlgebra 𝒪 Δ) PP := by
  letI := moduleΛ L S H 𝒪 k fam hcomm θbar Sp i₀ ι
  refine ⟨fun a c m => ?_⟩
  rw [Λsmul_def, Λsmul_def, map_smul, Algebra.smul_def, map_mul, Module.End.mul_apply, actP_algebraMap]

theorem coe_of_smul {H' : Subgroup (ZMod L)ˣ} (π : (ZMod L)ˣ →* Δ)
    (dG : ↥H' → G) (hdG : ∀ u : ↥H', fam (dG u) = Gen.dia (u : (ZMod L)ˣ))
    (hι : ∀ u : ↥H', ι (MonoidAlgebra.of 𝒪 Δ (π u)) =
      Sp.toCornerRing i₀ (gOp L S H 𝒪 k fam hcomm θbar (dG u)))
    (u : ↥H') (m : PP) :
    (((letI := moduleΛ L S H 𝒪 k fam hcomm θbar Sp i₀ ι; (MonoidAlgebra.of 𝒪 Δ (π u)) • m) : PP) : H1 L H 𝒪) =
      diamondL L H 𝒪 u (m : H1 L H 𝒪) := by
  rw [coe_Λsmul, hι u,
    coe_cornerRing_smul_of_mem L S H 𝒪 k fam hcomm θbar Sp i₀ _ (mem_corner L S H 𝒪 k fam hcomm θbar Sp i₀ m),
    dia_smul L S H 𝒪 k fam hcomm θbar (hdG u)]

def cornerEquiv : PP ≃ₗ[𝒪] ↥(IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀)) where
  toFun m := ⟨m, m.2⟩
  invFun m := ⟨m, m.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Corner

section Main

set_option maxHeartbeats 16000000 in
theorem main
    (L : ℕ) [NeZero L] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField 𝒪) p]
    (H H' : Subgroup (ZMod L)ˣ) (hHH' : H ≤ H') (hidx : ∃ n : ℕ, H.relIndex H' = p ^ n)
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
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hEis : ∃ (g : G) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L),
      φ g = CohCarrier.Gen.T ℓ hℓ hℓS hℓL ∧ ℓ ≡ 1 [MOD L] ∧
        θbar g ≠ (ℓ : IsLocalRing.ResidueField 𝒪) + 1)
    {Δ : Type} [CommGroup Δ] (π : (ZMod L)ˣ →* Δ)
    (hπ : ∀ δ : Δ, ∃ u ∈ H', π u = δ) (hπH : ∀ u ∈ H', (π u = 1 ↔ u ∈ H))
    (ι : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] Sp.CornerRing i₀)
    (hι : ∀ u : ↥H', ι (MonoidAlgebra.of 𝒪 Δ (π u)) = Sp.toCornerRing i₀
      ⟨(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).op (dG u),
        Algebra.subset_adjoin (Set.mem_range_self (dG u))⟩) :
    ∃ b : Fin (Module.finrank 𝒪
        ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀'))) →
          ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)),
      (∀ x : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)),
        ∃ c : Fin (Module.finrank 𝒪
            ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀'))) →
              MonoidAlgebra 𝒪 Δ,
          x = ∑ i, ι (c i) • b i) ∧
      (∀ c : Fin (Module.finrank 𝒪
            ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀'))) →
              MonoidAlgebra 𝒪 Δ,
        ∑ i, ι (c i) • b i = 0 ↔ ∀ i, c i = 0) := by
  classical

  letI := moduleΛ L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀ ι
  haveI := isScalarTower_Λ L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀ ι
  let P : Type := Pc L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀
  let P' : Type := Pc L S H' 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar Sp' i₀'
  let eP := cornerEquiv L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀
  let eP' := cornerEquiv L S H' 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar Sp' i₀'
  let d : ℕ := Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀'))
  have hd : d = Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀')) :=
    rfl

  have h : LevelLE L L H' H 1 :=
    { dvd := dvd_rfl
      ddvd := one_dvd _
      red := fun u hu => by rw [ZMod.unitsMap_self]; exact hHH' hu }

  obtain ⟨hmap, hker, -⟩ :=
    CohCarrier.map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily L S 𝒪
      H H' h r hrL hr hH' φ dG hdG hcomm hcomm' θbar Sp i₀ πk hπk Sp' i₀' πk' hπk'
  have hrank :=
    CohCarrier.finrank_cornerSubmodule_H1_eq_relIndex_mul_of_not_isEisenstein_subfamily L S 𝒪 p
      H H' hHH' hidx r hrL hr hH' φ dG hdG hcomm hcomm' θbar Sp i₀ πk hπk Sp' i₀' πk' hπk' hEis

  have hMtf : ∀ (H₀ : Subgroup (ZMod L)ˣ), Module.IsTorsionFree 𝒪 (H1 L H₀ 𝒪) := fun H₀ => by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c φ hc => ?_
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    · right
      refine AddMonoidHom.ext fun a => ?_
      have := DFunLike.congr_fun hc a
      rw [AddMonoidHom.smul_apply, AddMonoidHom.zero_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hc0
  haveI : Module.Finite 𝒪 (H1 L H 𝒪) := CohCarrier.H1_moduleFinite L H 𝒪 𝒪
  haveI : Module.Finite 𝒪 (H1 L H' 𝒪) := CohCarrier.H1_moduleFinite L H' 𝒪 𝒪
  haveI := hMtf H
  haveI := hMtf H'
  have hinclinj := incl_injective L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀
  have hinclinj' := incl_injective L S H' 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar Sp' i₀'
  haveI hPfin : Module.Finite 𝒪 P := Module.Finite.of_injective _ hinclinj
  haveI hP'fin : Module.Finite 𝒪 P' := Module.Finite.of_injective _ hinclinj'
  haveI hPtf : Module.IsTorsionFree 𝒪 P := hinclinj.moduleIsTorsionFree _ (fun c m => rfl)
  haveI hP'tf : Module.IsTorsionFree 𝒪 P' := hinclinj'.moduleIsTorsionFree _ (fun c m => rfl)

  haveI : Finite Δ := finite_Δ H' π hπ
  letI : Fintype Δ := Fintype.ofFinite Δ
  have hcardΔ : Fintype.card Δ = H.relIndex H' := by
    rw [← Nat.card_eq_fintype_card, natCard_Δ H H' π hπ hπH]
  have hΔ : ∀ g : Δ, ∃ n : ℕ, g ^ (p ^ n) = 1 := fun g => by
    obtain ⟨n, hn⟩ := hidx
    exact ⟨n, by rw [← hn, ← hcardΔ, pow_card_eq_one]⟩
  have hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪 := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero (IsLocalRing.ResidueField 𝒪) p

  have hfin' : Module.finrank 𝒪 P' = d := by rw [hd]; exact eP'.finrank_eq
  have hfin : Module.finrank 𝒪 P = d * Fintype.card Δ := by
    rw [eP.finrank_eq, hrank, hcardΔ, hd, mul_comm]
  let B : Module.Basis (Fin (d * Fintype.card Δ)) 𝒪 P := (Module.finBasis 𝒪 P).reindex (finCongr hfin)
  let b₀ : Module.Basis (Fin d) 𝒪 P' := (Module.finBasis 𝒪 P').reindex (finCongr hfin')
  have hBspan : ∀ x : P, ∃ a : Fin (d * Fintype.card Δ) → 𝒪, x = ∑ i, a i • B i :=
    fun x => ⟨fun i => B.repr x i, (B.sum_repr x).symm⟩
  have hBrel : ∀ a : Fin (d * Fintype.card Δ) → 𝒪, ∑ i, a i • B i = 0 ↔ ∀ i, a i = 0 := fun a =>
    ⟨fun h0 => Fintype.linearIndependent_iff.1 B.linearIndependent a h0,
      fun h0 => Finset.sum_eq_zero fun i _ => by rw [h0 i, zero_smul]⟩
  have hb₀span : ∀ x : P', ∃ a : Fin d → 𝒪, x = ∑ i, a i • b₀ i :=
    fun x => ⟨fun i => b₀.repr x i, (b₀.sum_repr x).symm⟩

  have hmapmem : ∀ m : P, CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h (m : H1 L H 𝒪) ∈
      IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀') := fun m => by
    have : CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h (m : H1 L H 𝒪) ∈
        Submodule.map (CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h)
          ((IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)).restrictScalars 𝒪) :=
      Submodule.mem_map_of_mem m.2
    rw [hmap] at this
    exact this
  let lam : P →ₗ[𝒪] P' :=
    { toFun := fun m => ⟨CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h (m : H1 L H 𝒪), hmapmem m⟩
      map_add' := fun x y => Subtype.ext (by
        show CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h ((x : H1 L H 𝒪) + y) = _
        rw [map_add]; rfl)
      map_smul' := fun c x => Subtype.ext (by
        show CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h (c • (x : H1 L H 𝒪)) = _
        rw [LinearMap.map_smul]; rfl) }
  have hlam_apply : ∀ m : P, ((lam m : P') : H1 L H' 𝒪) =
      CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h (m : H1 L H 𝒪) := fun m => rfl
  have hlam_surj : Function.Surjective lam := fun y => by
    have hy : (y : H1 L H' 𝒪) ∈ Submodule.map (CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h)
        ((IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)).restrictScalars 𝒪) := by
      rw [hmap]; exact y.2
    obtain ⟨m, hm, hmy⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨m, hm⟩, Subtype.ext hmy⟩

  have hι' : ∀ u : ↥H', ι (MonoidAlgebra.of 𝒪 Δ (π u)) =
      Sp.toCornerRing i₀ (gOp L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar (dG u)) := hι
  have hgens : Submodule.map (incl L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀)
      (Submodule.span 𝒪 {z : P | ∃ (δ : Δ) (x : P), z = (MonoidAlgebra.of 𝒪 Δ δ) • x - x}) =
      Submodule.span 𝒪 {y : H1 L H 𝒪 | ∃ u ∈ H',
        ∃ x ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀),
          y = diamondL L H 𝒪 u x - x} := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨δ, x, rfl⟩, rfl⟩
      obtain ⟨u, hu, rfl⟩ := hπ δ
      refine ⟨u, hu, x, x.2, ?_⟩
      rw [incl_apply, Submodule.coe_sub,
        coe_of_smul L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀ ι π dG hdG hι' ⟨u, hu⟩ x]
    · rintro ⟨u, hu, x, hx, rfl⟩
      refine ⟨(MonoidAlgebra.of 𝒪 Δ (π u)) • (⟨x, hx⟩ : P) - ⟨x, hx⟩, ⟨π u, ⟨x, hx⟩, rfl⟩, ?_⟩
      rw [incl_apply, Submodule.coe_sub,
        coe_of_smul L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀ ι π dG hdG hι' ⟨u, hu⟩ ⟨x, hx⟩]
  have hlam_ker : ∀ m : P, lam m = 0 ↔
      m ∈ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ))) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) P) := fun m => by
    rw [show (lam m = 0 ↔ CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h (m : H1 L H 𝒪) = 0) from
      ⟨fun h0 => by rw [← hlam_apply, h0]; rfl, fun h0 => Subtype.ext h0⟩]
    rw [hker (m : H1 L H 𝒪) m.2, mem_augSmul_iff m, ← hgens]
    constructor
    · intro hm
      obtain ⟨m', hm', hmm'⟩ := Submodule.mem_map.1 hm
      rwa [← hinclinj hmm']
    · intro hm
      exact Submodule.mem_map_of_mem hm

  obtain ⟨b, hbspan, hbrel⟩ :=
    TW12.exists_groupAlgebra_basis_of_descent (𝒪 := 𝒪) hp Δ hΔ P d (fun i => B i) hBspan hBrel
      P' lam.toAddMonoidHom (fun a m => lam.map_smul a m) hlam_surj hlam_ker (fun i => b₀ i) hb₀span

  have hcoe : ∀ (c : MonoidAlgebra 𝒪 Δ) (m : P),
      ((ι c • eP m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀))) : H1 L H 𝒪) =
        ((c • m : P) : H1 L H 𝒪) := fun c m => rfl
  have hsum : ∀ (c : Fin d → MonoidAlgebra 𝒪 Δ),
      ((∑ i, ι (c i) • eP (b i) : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀))) :
        H1 L H 𝒪) = ((∑ i, c i • b i : P) : H1 L H 𝒪) := fun c => by
    rw [Submodule.coe_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => hcoe (c i) (b i)
  refine ⟨fun i => eP (b i), fun x => ?_, fun c => ?_⟩
  · obtain ⟨c, hc⟩ := hbspan (eP.symm x)
    refine ⟨c, Subtype.ext ?_⟩
    rw [hsum, ← hc]
    rfl
  · rw [← hbrel c]
    constructor
    · intro h0
      apply hinclinj
      rw [incl_apply, ← hsum, h0, incl_apply]
      rfl
    · intro h0
      apply Subtype.ext
      rw [hsum, h0]
      rfl

end Main

end U5FreeSubSol
p2m_reactivate "P2MW.S_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily.U5FreeSubSol"

end
p2m_reactivate "P2MW.S_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily.U5FreeSubSol"

open scoped IsMulCommutative in
theorem solution
    (L : ℕ) [NeZero L] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField 𝒪) p]
    (H H' : Subgroup (ZMod L)ˣ) (hHH' : H ≤ H') (hidx : ∃ n : ℕ, H.relIndex H' = p ^ n)
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
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)

    (hEis : ∃ (g : G) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L),
      φ g = CohCarrier.Gen.T ℓ hℓ hℓS hℓL ∧ ℓ ≡ 1 [MOD L] ∧
        θbar g ≠ (ℓ : IsLocalRing.ResidueField 𝒪) + 1)

    {Δ : Type} [CommGroup Δ] (π : (ZMod L)ˣ →* Δ)
    (hπ : ∀ δ : Δ, ∃ u ∈ H', π u = δ) (hπH : ∀ u ∈ H', (π u = 1 ↔ u ∈ H))
    (ι : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] Sp.CornerRing i₀)
    (hι : ∀ u : ↥H', ι (MonoidAlgebra.of 𝒪 Δ (π u)) = Sp.toCornerRing i₀
      ⟨(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).op (dG u),
        Algebra.subset_adjoin (Set.mem_range_self (dG u))⟩) :
    ∃ b : Fin (Module.finrank 𝒪
        ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀'))) →
          ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)),
      (∀ x : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)),
        ∃ c : Fin (Module.finrank 𝒪
            ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀'))) →
              MonoidAlgebra 𝒪 Δ,
          x = ∑ i, ι (c i) • b i) ∧
      (∀ c : Fin (Module.finrank 𝒪
            ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀'))) →
              MonoidAlgebra 𝒪 Δ,
        ∑ i, ι (c i) • b i = 0 ↔ ∀ i, c i = 0) :=
  U5FreeSubSol.main L S 𝒪 p H H' hHH' hidx r hrL hr hH' φ dG hdG hcomm hcomm' θbar Sp i₀ πk hπk
    Sp' i₀' πk' hπk' hEis π hπ hπH ι hι

end S_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily
end P2MW
export P2MW.S_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily (solution)
