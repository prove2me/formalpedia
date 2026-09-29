-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c09db11b-e8f4-51ba-baf9-771b1fbfe6bc

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
import Theorems.Thm_LT_LatticeTree_FullLattice_eq_of_forall_smul_mem_of_le_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace ShareVertex

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

abbrev tgt (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (A : FullLattice 𝒪 K) :
    Submodule B (latticeBaseChange 𝒪 K B A) :=
  d.line A ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B A))

def W (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (A : FullLattice 𝒪 K) : Submodule 𝒪 (Fin 2 → K) where
  carrier := {v | ∃ hv : v ∈ A.1, (1 : B) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥A.1) ∈ tgt d 𝔭 A}
  zero_mem' := ⟨A.1.zero_mem, by
    have : (⟨0, A.1.zero_mem⟩ : ↥A.1) = 0 := rfl
    rw [this, tmul_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    refine ⟨A.1.add_mem hv hw, ?_⟩
    have : (⟨v + w, A.1.add_mem hv hw⟩ : ↥A.1) = ⟨v, hv⟩ + ⟨w, hw⟩ := rfl
    rw [this, tmul_add]; exact Submodule.add_mem _ hv' hw'
  smul_mem' := by
    rintro r v ⟨hv, hv'⟩
    refine ⟨A.1.smul_mem r hv, ?_⟩
    have : (⟨r • v, A.1.smul_mem r hv⟩ : ↥A.1) = r • ⟨v, hv⟩ := rfl
    rw [this, tmul_smul, ← algebraMap_smul B r]
    exact Submodule.smul_mem _ _ hv'

theorem mem_W {d : DeligneDatum (K := K) π B} {𝔭 : Ideal B} {A : FullLattice 𝒪 K} {v : Fin 2 → K} :
    v ∈ W d 𝔭 A ↔ ∃ hv : v ∈ A.1, (1 : B) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥A.1) ∈ tgt d 𝔭 A := Iff.rfl

theorem mem_W_of_mem {d : DeligneDatum (K := K) π B} {𝔭 : Ideal B} {A : FullLattice 𝒪 K} (v : ↥A.1)
    (h : (1 : B) ⊗ₜ[𝒪] v ∈ tgt d 𝔭 A) : (v : Fin 2 → K) ∈ W d 𝔭 A := ⟨v.2, h⟩

theorem tmul_mem_of_mem_W {d : DeligneDatum (K := K) π B} {𝔭 : Ideal B} {A : FullLattice 𝒪 K} (v : ↥A.1)
    (h : (v : Fin 2 → K) ∈ W d 𝔭 A) : (1 : B) ⊗ₜ[𝒪] v ∈ tgt d 𝔭 A := by
  obtain ⟨hv, h⟩ := h; exact h

theorem W_le (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (A : FullLattice 𝒪 K) : W d 𝔭 A ≤ A.1 :=
  fun _ ⟨hv, _⟩ => hv

theorem pi_smul_mem_W (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (h𝔭 : algebraMap 𝒪 B π ∈ 𝔭)
    (A : FullLattice 𝒪 K) (v : Fin 2 → K) (hv : v ∈ A.1) : algebraMap 𝒪 K π • v ∈ W d 𝔭 A := by
  have hmem : algebraMap 𝒪 K π • v ∈ A.1 := by rw [algebraMap_smul]; exact A.1.smul_mem π hv
  refine ⟨hmem, ?_⟩
  have : (⟨algebraMap 𝒪 K π • v, hmem⟩ : ↥A.1) = π • ⟨v, hv⟩ := by
    apply Subtype.ext; simp [algebraMap_smul]
  rw [this, tmul_smul, ← algebraMap_smul B π]
  exact Submodule.mem_sup_right (Submodule.smul_mem_smul h𝔭 Submodule.mem_top)

theorem W_ne (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) [𝔭.IsPrime] (A : FullLattice 𝒪 K) :
    W d 𝔭 A ≠ A.1 := by
  intro hW
  haveI := d.invertible A

  have htop : tgt d 𝔭 A = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul b v =>
      have hv : (v : Fin 2 → K) ∈ W d 𝔭 A := by rw [hW]; exact v.2
      have h1 := tmul_mem_of_mem_W v hv
      have : b ⊗ₜ[𝒪] v = b • ((1 : B) ⊗ₜ[𝒪] v) := by rw [smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ _ h1

  have hQ : (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B A ⧸ d.line A)) = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (d.line A) q
    have hx : x ∈ tgt d 𝔭 A := by rw [htop]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hy0 : (d.line A).mkQ y = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hy
    rw [map_add, hy0, zero_add]
    have : (d.line A).mkQ z ∈ ((𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B A))).map (d.line A).mkQ :=
      Submodule.mem_map_of_mem hz
    rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this

  have hfg : (⊤ : Submodule B (latticeBaseChange 𝒪 K B A ⧸ d.line A)).FG := Module.Finite.fg_top
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔭 ⊤ hfg (by rw [hQ])
  have hr0 : r = 0 := by
    have hinj := (Module.Invertible.toModuleEnd_bijective B (latticeBaseChange 𝒪 K B A ⧸ d.line A)).1
    apply hinj
    refine LinearMap.ext fun q => ?_
    rw [map_zero, LinearMap.zero_apply]
    exact hr q Submodule.mem_top
  rw [hr0, zero_sub] at hr1
  exact (Ideal.IsPrime.ne_top ‹𝔭.IsPrime›) ((Ideal.eq_top_iff_one _).mpr (by simpa using 𝔭.neg_mem hr1))

theorem not_W_le_of_not_vertexNondegAt [IsDomain 𝒪] [IsFractionRing 𝒪 K] (hπ : Irreducible π) (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B)
    (A : FullLattice 𝒪 K) (hV : ¬ d.VertexNondegAt π 𝔭 A) :
    ¬ (W d 𝔭 A ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) A.1) := by
  intro hle
  apply hV
  intro v hv hmem
  have hW : (v : Fin 2 → K) ∈ W d 𝔭 A := mem_W_of_mem v hmem
  obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp (hle hW)
  exact hv ⟨⟨w, hw⟩, by rw [← hwv, unitOfNeZero_coe]⟩

theorem W_mono (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (A A' : FullLattice 𝒪 K) (h : A'.1 ≤ A.1) :
    W d 𝔭 A' ≤ W d 𝔭 A := by
  rintro v ⟨hv, hv'⟩
  refine ⟨h hv, ?_⟩
  have himg : inclBaseChange B h ((1 : B) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥A'.1)) = (1 : B) ⊗ₜ[𝒪] (⟨v, h hv⟩ : ↥A.1) := rfl
  rw [← himg]
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv'
  rw [← hyz, map_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (d.mono h (Submodule.mem_map_of_mem hy)))
    (Submodule.mem_sup_right ?_)
  have : inclBaseChange B h z ∈ ((𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B A'))).map (inclBaseChange B h) :=
    Submodule.mem_map_of_mem hz
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono (le_refl 𝔭) le_top this

theorem W_act_scalarGL (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (c : Kˣ) (A : FullLattice 𝒪 K) :
    W d 𝔭 (FullLattice.act (scalarGL c) A) = latticeMap (scalarGL c) (W d 𝔭 A) := by
  set e := actBaseChange B (scalarGL c) A with he

  have htgt : tgt d 𝔭 (FullLattice.act (scalarGL c) A) = (tgt d 𝔭 A).map e.toLinearMap := by
    show d.line (FullLattice.act (scalarGL c) A) ⊔ _ = _
    rw [d.homothety c A, Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

  have hkey : ∀ (w : ↥A.1), e ((1 : B) ⊗ₜ[𝒪] w) = (1 : B) ⊗ₜ[𝒪] (latticeMapEquiv (scalarGL c) A.1 w) := fun w => rfl
  have hcoe : ∀ (w : ↥A.1), ((latticeMapEquiv (scalarGL c) A.1 w : ↥(latticeMap (scalarGL c) A.1)) : Fin 2 → K) =
      (c : K) • (w : Fin 2 → K) := fun w => by rw [coe_latticeMapEquiv_apply, scalarGL_mulVec]
  ext v
  rw [mem_W, mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨hv, hmem⟩
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp hv
    refine ⟨w, ⟨hw, ?_⟩, hwv⟩
    have hsub : (⟨v, hv⟩ : ↥(FullLattice.act (scalarGL c) A).1) = latticeMapEquiv (scalarGL c) A.1 ⟨w, hw⟩ := by
      apply Subtype.ext; rw [hcoe]; exact hwv.symm
    rw [hsub] at hmem
    change e ((1 : B) ⊗ₜ[𝒪] (⟨w, hw⟩ : ↥A.1)) ∈ tgt d 𝔭 (FullLattice.act (scalarGL c) A) at hmem
    rw [htgt, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] at hmem
    exact hmem
  · rintro ⟨w, ⟨hw, hmem⟩, hwv⟩
    have hv : v ∈ (FullLattice.act (scalarGL c) A).1 := mem_latticeMap_scalarGL.mpr ⟨w, hw, hwv⟩
    refine ⟨hv, ?_⟩
    have hsub : (⟨v, hv⟩ : ↥(FullLattice.act (scalarGL c) A).1) = latticeMapEquiv (scalarGL c) A.1 ⟨w, hw⟩ := by
      apply Subtype.ext; rw [hcoe]; exact hwv.symm
    rw [hsub]
    change e ((1 : B) ⊗ₜ[𝒪] (⟨w, hw⟩ : ↥A.1)) ∈ tgt d 𝔭 (FullLattice.act (scalarGL c) A)
    rw [htgt, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    exact hmem

theorem edge_read [IsDomain 𝒪] [IsFractionRing 𝒪 K] (hπ : Irreducible π) (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B)
    (M' M : FullLattice 𝒪 K) (h : d.EdgeNondegAt π 𝔭 M' M) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 ≤ M'.1 ∧ M'.1 ≤ M.1 ∧
      W d 𝔭 M ≤ M'.1 ∧ W d 𝔭 M' ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 := by
  obtain ⟨hle, hπM, h3, h4⟩ := h
  refine ⟨?_, hle, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    rw [unitOfNeZero_coe]; exact hπM ⟨w, hw⟩
  · rintro v ⟨hv, hmem⟩
    by_contra hnot
    exact h3 ⟨v, hv⟩ hnot hmem
  · rintro v ⟨hv, hmem⟩
    by_contra hnot
    refine h4 ⟨v, hv⟩ ?_ hmem
    rintro ⟨w, hww⟩
    exact hnot (mem_latticeMap_scalarGL.mpr ⟨w, w.2, by rw [unitOfNeZero_coe]; exact hww.symm⟩)

theorem latticeMap_scalarGL_of_eq_of_eq
    {P X Y : Submodule 𝒪 (Fin 2 → K)} {c c' : Kˣ}
    (hX : latticeMap (scalarGL c) P = X) (hY : latticeMap (scalarGL c') P = Y) :
    latticeMap (scalarGL (c' * c⁻¹)) X = Y := by
  rw [← hX, ← hY, ← latticeMap_mul, ← scalarGL_mul, mul_assoc, inv_mul_cancel, mul_one]

end ShareVertex

end

namespace ShareVertex

namespace Aux

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}

theorem algebraMap_ne_zero' (hπ : Irreducible π) : algebraMap 𝒪 K π ≠ 0 :=
  fun h => hπ.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K)).mp h)

theorem exists_pow_isInteger (hπ : Irreducible π) (s : Finset K) :
    ∃ k : ℕ, ∀ c ∈ s, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ k) * c) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors 𝒪) s id
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hπ
  refine ⟨k, fun c hc => ?_⟩
  have := hb c hc
  rw [id, Algebra.smul_def, hu, map_mul, mul_assoc] at this
  obtain ⟨r, hr⟩ := this
  refine ⟨↑u⁻¹ * r, ?_⟩
  rw [map_mul, hr, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem exists_pow_isInteger_apply (hπ : Irreducible π) (M : FullLattice 𝒪 K) :
    ∃ k : ℕ, ∀ v ∈ M.1, ∀ i, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ k) * v i) := by
  classical
  obtain ⟨S, hS⟩ := M.2.1
  obtain ⟨k, hk⟩ := exists_pow_isInteger (K := K) hπ (S.biUnion fun v => {v 0, v 1})
  refine ⟨k, fun v hv => ?_⟩
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    intro i
    apply hk
    rw [Finset.mem_biUnion]
    refine ⟨w, hw, ?_⟩
    fin_cases i <;> simp
  | zero => intro i; rw [Pi.zero_apply, mul_zero]; exact IsLocalization.isInteger_zero
  | add a b _ _ ha hb => intro i; rw [Pi.add_apply, mul_add]; exact IsLocalization.isInteger_add (ha i) (hb i)
  | smul r a _ ha =>
    intro i
    rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]
    exact IsLocalization.isInteger_mul ⟨r, rfl⟩ (ha i)

theorem exists_pow_smul_single_mem (hπ : Irreducible π) (M : FullLattice 𝒪 K) (i : Fin 2) :
    ∃ k : ℕ, algebraMap 𝒪 K (π ^ k) • (Pi.single i 1 : Fin 2 → K) ∈ M.1 := by
  classical
  have hmem : (Pi.single i 1 : Fin 2 → K) ∈ Submodule.span K (M.1 : Set (Fin 2 → K)) := by
    rw [M.2.2]; exact Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.mp hmem
  obtain ⟨k, hk⟩ := exists_pow_isInteger (K := K) hπ (c.support.image c)
  refine ⟨k, ?_⟩
  rw [← hsum, Finsupp.sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun w hw => ?_
  rw [smul_smul]
  obtain ⟨r, hr⟩ := hk (c w) (Finset.mem_image_of_mem c hw)
  rw [← hr, algebraMap_smul]
  exact Submodule.smul_mem _ r (hc (Finset.mem_coe.mpr hw))

theorem pow_smul_single_mem_of_le (M : FullLattice 𝒪 K) (i : Fin 2) {k k' : ℕ} (hk : k ≤ k')
    (h : algebraMap 𝒪 K (π ^ k) • (Pi.single i 1 : Fin 2 → K) ∈ M.1) :
    algebraMap 𝒪 K (π ^ k') • (Pi.single i 1 : Fin 2 → K) ∈ M.1 := by
  have : algebraMap 𝒪 K (π ^ k') • (Pi.single i 1 : Fin 2 → K) =
      (π ^ (k' - k)) • (algebraMap 𝒪 K (π ^ k) • (Pi.single i 1 : Fin 2 → K)) := by
    rw [algebraMap_smul, algebraMap_smul, smul_smul, ← pow_add, Nat.sub_add_cancel hk]
  rw [this]
  exact Submodule.smul_mem _ _ h

theorem not_isInteger_zpow_neg (hπ : Irreducible π) (m : ℕ) (hm : 0 < m) :
    ¬ IsLocalization.IsInteger 𝒪 ((algebraMap 𝒪 K π) ^ (-(m : ℤ))) := by
  rintro ⟨r, hr⟩
  rw [zpow_neg, zpow_natCast, ← map_pow] at hr
  have hπm : algebraMap 𝒪 K (π ^ m) ≠ 0 :=
    fun h => pow_ne_zero m hπ.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K)).mp h)
  have h1 : algebraMap 𝒪 K (r * π ^ m) = 1 := by
    rw [map_mul, hr, inv_mul_cancel₀ hπm]
  rw [← (algebraMap 𝒪 K).map_one] at h1
  have h2 : r * π ^ m = 1 := IsFractionRing.injective 𝒪 K h1
  have : IsUnit (π ^ m) := isUnit_iff_exists_inv'.2 ⟨r, h2⟩
  exact hπ.not_isUnit ((isUnit_pow_iff hm.ne').1 this)

theorem exists_unit_normalize (hπ : Irreducible π) (L M : FullLattice 𝒪 K) :
    ∃ c : Kˣ, (∀ v ∈ L.1, (c : K) • v ∈ M.1) ∧
      ∃ v ∈ L.1, ¬ ∃ w ∈ M.1, (c : K) • v = (algebraMap 𝒪 K π) • w := by
  classical
  set u : Kˣ := unitOfNeZero (K := K) hπ.ne_zero with hu
  have huK : (u : K) = algebraMap 𝒪 K π := rfl
  have hπK : algebraMap 𝒪 K π ≠ 0 := algebraMap_ne_zero' hπ

  set P : ℤ → Prop := fun j => ∀ v ∈ L.1, ((u ^ j : Kˣ) : K) • v ∈ M.1 with hP

  obtain ⟨a, ha⟩ := exists_pow_isInteger_apply (K := K) hπ L
  obtain ⟨b0, hb0⟩ := exists_pow_smul_single_mem (K := K) hπ M 0
  obtain ⟨b1, hb1⟩ := exists_pow_smul_single_mem (K := K) hπ M 1
  have hb0' := pow_smul_single_mem_of_le M 0 (le_max_left b0 b1) hb0
  have hb1' := pow_smul_single_mem_of_le M 1 (le_max_right b0 b1) hb1
  set b := max b0 b1 with hb
  have hne : ∃ j, P j := by
    refine ⟨((a + b : ℕ) : ℤ), fun v hv => ?_⟩
    rw [zpow_natCast, Units.val_pow_eq_pow_val, huK, ← map_pow]
    obtain ⟨r0, hr0⟩ := ha v hv 0
    obtain ⟨r1, hr1⟩ := ha v hv 1
    have key : algebraMap 𝒪 K (π ^ (a + b)) • v =
        (algebraMap 𝒪 K (π ^ a) * v 0) • (algebraMap 𝒪 K (π ^ b) • (Pi.single 0 1 : Fin 2 → K)) +
          (algebraMap 𝒪 K (π ^ a) * v 1) • (algebraMap 𝒪 K (π ^ b) • (Pi.single 1 1 : Fin 2 → K)) := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, pow_add, map_mul]
      fin_cases i <;> simp <;> ring
    have e0 : algebraMap 𝒪 K r0 • (algebraMap 𝒪 K (π ^ b) • (Pi.single 0 1 : Fin 2 → K)) =
        r0 • (algebraMap 𝒪 K (π ^ b) • (Pi.single 0 1 : Fin 2 → K)) := algebraMap_smul K r0 _
    have e1 : algebraMap 𝒪 K r1 • (algebraMap 𝒪 K (π ^ b) • (Pi.single 1 1 : Fin 2 → K)) =
        r1 • (algebraMap 𝒪 K (π ^ b) • (Pi.single 1 1 : Fin 2 → K)) := algebraMap_smul K r1 _
    rw [key, ← hr0, ← hr1, e0, e1]
    exact M.1.add_mem (M.1.smul_mem r0 hb0') (M.1.smul_mem r1 hb1')

  obtain ⟨a', ha'⟩ := exists_pow_isInteger_apply (K := K) hπ M
  obtain ⟨b', hb'⟩ := exists_pow_smul_single_mem (K := K) hπ L 0
  have hbdd : ∃ lb : ℤ, ∀ j, P j → lb ≤ j := by
    refine ⟨-((a' + b' : ℕ) : ℤ), fun j hj => ?_⟩
    by_contra hlt
    push Not at hlt
    have hmem := hj _ hb'
    have hint := ha' _ hmem 0
    rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, smul_eq_mul, mul_one,
      Units.val_zpow_eq_zpow_val, huK, map_pow, map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hπK,
      ← zpow_add₀ hπK] at hint

    obtain ⟨m, hm⟩ : ∃ m : ℕ, (a' : ℤ) + (j + (b' : ℤ)) = -(m : ℤ) ∧ 0 < m := by
      refine ⟨(-( (a' : ℤ) + (j + (b' : ℤ)))).toNat, ?_, ?_⟩
      · rw [Int.toNat_of_nonneg (by push_cast at hlt; omega)]; ring
      · have : ( -((a' : ℤ) + (j + (b' : ℤ)))) > 0 := by push_cast at hlt; omega
        exact (Int.lt_toNat.2 (by simpa using this))
    rw [hm.1] at hint
    exact not_isInteger_zpow_neg hπ m hm.2 hint
  obtain ⟨j₀, hj₀, hmin⟩ := Int.exists_least_of_bdd hbdd hne
  refine ⟨u ^ j₀, hj₀, ?_⟩
  by_contra hall
  push Not at hall

  have : P (j₀ - 1) := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := hall v hv
    have : ((u ^ (j₀ - 1) : Kˣ) : K) • v = w := by
      rw [zpow_sub_one, Units.val_mul, mul_comm, ← smul_smul, hvw, Units.val_inv_eq_inv_val, huK, smul_smul,
        inv_mul_cancel₀ hπK, one_smul]
    rw [this]; exact hw
  have := hmin _ this
  omega

theorem exists_pow_smul_mem (hπ : Irreducible π) (X Z : FullLattice 𝒪 K) :
    ∃ n : ℕ, ∀ z ∈ Z.1, algebraMap 𝒪 K (π ^ n) • z ∈ X.1 := by
  obtain ⟨a, ha⟩ := exists_pow_isInteger_apply (K := K) hπ Z
  obtain ⟨b0, hb0⟩ := exists_pow_smul_single_mem (K := K) hπ X 0
  obtain ⟨b1, hb1⟩ := exists_pow_smul_single_mem (K := K) hπ X 1
  have hb0' := pow_smul_single_mem_of_le X 0 (le_max_left b0 b1) hb0
  have hb1' := pow_smul_single_mem_of_le X 1 (le_max_right b0 b1) hb1
  refine ⟨a + max b0 b1, fun v hv => ?_⟩
  obtain ⟨r0, hr0⟩ := ha v hv 0
  obtain ⟨r1, hr1⟩ := ha v hv 1
  have key : algebraMap 𝒪 K (π ^ (a + max b0 b1)) • v =
      (algebraMap 𝒪 K (π ^ a) * v 0) • (algebraMap 𝒪 K (π ^ max b0 b1) • (Pi.single 0 1 : Fin 2 → K)) +
        (algebraMap 𝒪 K (π ^ a) * v 1) • (algebraMap 𝒪 K (π ^ max b0 b1) • (Pi.single 1 1 : Fin 2 → K)) := by
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, pow_add, map_mul]
    fin_cases i <;> simp <;> ring
  have e0 : algebraMap 𝒪 K r0 • (algebraMap 𝒪 K (π ^ max b0 b1) • (Pi.single 0 1 : Fin 2 → K)) =
      r0 • (algebraMap 𝒪 K (π ^ max b0 b1) • (Pi.single 0 1 : Fin 2 → K)) := algebraMap_smul K r0 _
  have e1 : algebraMap 𝒪 K r1 • (algebraMap 𝒪 K (π ^ max b0 b1) • (Pi.single 1 1 : Fin 2 → K)) =
      r1 • (algebraMap 𝒪 K (π ^ max b0 b1) • (Pi.single 1 1 : Fin 2 → K)) := algebraMap_smul K r1 _
  rw [key, ← hr0, ← hr1, e0, e1]
  exact X.1.add_mem (X.1.smul_mem r0 hb0') (X.1.smul_mem r1 hb1')

theorem sc_le (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL c) X ≤ X := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.1 hv
  rw [hc, algebraMap_smul]
  exact X.smul_mem π hw

theorem smul_mem_sc (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) {X : Submodule 𝒪 (Fin 2 → K)} {v : Fin 2 → K}
    (hv : v ∈ X) : algebraMap 𝒪 K π • v ∈ latticeMap (scalarGL c) X :=
  mem_latticeMap_scalarGL.2 ⟨v, hv, by rw [hc]⟩

theorem forall_ne_of_not_mem_sc (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) {X : Submodule 𝒪 (Fin 2 → K)}
    {v : Fin 2 → K} (hv : v ∉ latticeMap (scalarGL c) X) : ∀ w ∈ X, v ≠ algebraMap 𝒪 K π • w := by
  intro w hw h
  exact hv (mem_latticeMap_scalarGL.2 ⟨w, hw, by rw [hc, h]⟩)

theorem sc_sup (g : Matrix.GeneralLinearGroup (Fin 2) K) (X Y : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap g (X ⊔ Y) = latticeMap g X ⊔ latticeMap g Y :=
  Submodule.map_sup _ _ _

theorem sc_comm (c c' : Kˣ) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL c) (latticeMap (scalarGL c') X) = latticeMap (scalarGL c') (latticeMap (scalarGL c) X) := by
  rw [← latticeMap_mul, ← latticeMap_mul, ← scalarGL_mul, ← scalarGL_mul, mul_comm]

theorem sc_pow_pow (c : Kˣ) (a b : ℕ) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL (c ^ a)) (latticeMap (scalarGL (c ^ b)) X) = latticeMap (scalarGL (c ^ (a + b))) X := by
  rw [← latticeMap_mul, ← scalarGL_mul, ← pow_add]

theorem sc_pow_one (c : Kˣ) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL c) X = latticeMap (scalarGL (c ^ 1)) X := by
  rw [pow_one]

theorem sc_pow_le (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) (j : ℕ) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL (c ^ j)) X ≤ X := by
  induction j with
  | zero => rw [pow_zero, scalarGL_one, latticeMap_one]
  | succ j ih =>
    rw [pow_succ', scalarGL_mul, latticeMap_mul]
    exact (latticeMap_mono _ ih).trans (sc_le c hc X)

theorem pow_le_of_pow_le (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) {X Y : Submodule 𝒪 (Fin 2 → K)} {j : ℕ}
    (h : latticeMap (scalarGL (c ^ j)) X ≤ Y) (i : ℕ) : latticeMap (scalarGL (c ^ (i + j))) X ≤ Y := by
  induction i with
  | zero => rwa [zero_add]
  | succ i ih =>
    rw [Nat.succ_add, pow_succ', scalarGL_mul, latticeMap_mul]
    exact (latticeMap_mono _ ih).trans (sc_le c hc Y)

theorem absorb (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) (X Y : Submodule 𝒪 (Fin 2 → K))
    (h : Y ≤ X ⊔ latticeMap (scalarGL c) Y) (j : ℕ) :
    Y ≤ X ⊔ latticeMap (scalarGL (c ^ j)) (latticeMap (scalarGL c) Y) := by
  induction j with
  | zero => rwa [pow_zero, scalarGL_one, latticeMap_one]
  | succ j ih =>
    have h1 : latticeMap (scalarGL c) Y ≤ X ⊔ latticeMap (scalarGL (c ^ (j + 1))) (latticeMap (scalarGL c) Y) := by
      refine (latticeMap_mono (scalarGL c) ih).trans ?_
      rw [sc_sup, pow_succ', scalarGL_mul, latticeMap_mul]
      exact sup_le ((sc_le c hc X).trans le_sup_left) le_sup_right
    exact h.trans (sup_le le_sup_left h1)

theorem isFullLattice_sup (L : FullLattice 𝒪 K) (Y : Submodule 𝒪 (Fin 2 → K)) (hY : Y.FG) :
    IsFullLattice (L.1 ⊔ Y) := by
  refine ⟨L.2.1.sup hY, ?_⟩
  apply le_antisymm le_top
  rw [← L.2.2]
  exact Submodule.span_mono (fun x hx => Submodule.mem_sup_left hx)

def P1 (c : Kˣ) (N A : FullLattice 𝒪 K) : FullLattice 𝒪 K :=
  ⟨N.1 ⊔ latticeMap (scalarGL c) A.1, isFullLattice_sup N _ (A.2.map (scalarGL c)).1⟩

theorem P1_val (c : Kˣ) (N A : FullLattice 𝒪 K) : (P1 c N A).1 = N.1 ⊔ latticeMap (scalarGL c) A.1 := rfl

end Aux

open Aux

theorem lattice_walk
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    (W : FullLattice 𝒪 K → Submodule 𝒪 (Fin 2 → K))
    (hW_le : ∀ A : FullLattice 𝒪 K, W A ≤ A.1)
    (hW_ne : ∀ A : FullLattice 𝒪 K, W A ≠ A.1)
    (hπW : ∀ (A : FullLattice 𝒪 K) (v : Fin 2 → K), v ∈ A.1 → algebraMap 𝒪 K π • v ∈ W A)
    (hW_not : ∀ A : FullLattice 𝒪 K, ¬ (W A ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) A.1))
    (hW_mono : ∀ A A' : FullLattice 𝒪 K, A'.1 ≤ A.1 → W A' ≤ W A)
    (hW_hom : ∀ (c : Kˣ) (A : FullLattice 𝒪 K), W (FullLattice.act (scalarGL c) A) = latticeMap (scalarGL c) (W A))
    (M' M L' L : FullLattice 𝒪 K)
    (hM₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 ≤ M'.1) (hM₂ : M'.1 ≤ M.1)
    (hM₃ : W M ≤ M'.1) (hM₄ : W M' ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1)
    (hL₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) L.1 ≤ L'.1) (hL₂ : L'.1 ≤ L.1)
    (hL₃ : W L ≤ L'.1) (hL₄ : W L' ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) L.1) :
    ∃ (c : Kˣ) (X Y : FullLattice 𝒪 K), (X = M' ∨ X = M) ∧ (Y = L' ∨ Y = L) ∧
      latticeMap (scalarGL c) X.1 = Y.1 := by
  classical
  set u : Kˣ := unitOfNeZero (K := K) hπ.ne_zero with hu_def
  have hu : (u : K) = algebraMap 𝒪 K π := by rw [hu_def, unitOfNeZero_coe]

  have two_step : ∀ (A : FullLattice 𝒪 K) (R₁ R₂ : Submodule 𝒪 (Fin 2 → K)),
      (∀ v ∈ A.1, algebraMap 𝒪 K π • v ∈ R₁) → R₁ ≤ R₂ → R₂ ≤ A.1 →
      (∃ v ∈ R₁, v ∉ latticeMap (scalarGL u) A.1) → R₂ ≠ A.1 → R₁ = R₂ := by
    intro A R₁ R₂ h1 h2 h3 h4 h5
    obtain ⟨v, hv, hv'⟩ := h4
    exact LT.LatticeTree.FullLattice.eq_of_forall_smul_mem_of_le_of_le π hπ A R₁ R₂ h1 h2 h3
      ⟨v, hv, forall_ne_of_not_mem_sc u hu hv'⟩ h5
  have hW_ex : ∀ A : FullLattice 𝒪 K, ∃ v ∈ W A, v ∉ latticeMap (scalarGL u) A.1 := fun A =>
    SetLike.not_le_iff_exists.mp (hW_not A)
  have strict : ∀ A' A : FullLattice 𝒪 K, W A ≤ A'.1 → W A' ≤ latticeMap (scalarGL u) A.1 →
      A'.1 ≠ A.1 ∧ latticeMap (scalarGL u) A.1 ≠ A'.1 := by
    intro A' A h3 h4
    constructor
    · intro h
      apply hW_not A
      have hAA : A' = A := Subtype.ext h
      rw [hAA] at h4
      exact h4
    · intro h
      apply hW_not A
      rw [h]
      exact h3

  have mono_lemma : ∀ P Q : FullLattice 𝒪 K, latticeMap (scalarGL u) P.1 ≤ Q.1 → Q.1 ≤ P.1 →
      latticeMap (scalarGL u) P.1 ≠ Q.1 → Q.1 ≠ P.1 →
      W Q = latticeMap (scalarGL u) P.1 ∨ W P = Q.1 := by
    intro P Q hPQ hQP hne1 hne2
    by_cases h : W Q ≤ latticeMap (scalarGL u) P.1
    · left
      exact two_step Q (W Q) _ (hπW Q) h hPQ (hW_ex Q) hne1
    · right
      obtain ⟨v, hvW, hv⟩ := SetLike.not_le_iff_exists.mp h
      have hvP : v ∈ W P := hW_mono P Q hQP hvW
      have hvQ : v ∈ Q.1 := hW_le Q hvW
      have hin : ∀ w ∈ P.1, algebraMap 𝒪 K π • w ∈ W P ⊓ Q.1 := fun w hw =>
        Submodule.mem_inf.mpr ⟨hπW P w hw, hPQ (smul_mem_sc u hu hw)⟩
      have e1 : W P ⊓ Q.1 = W P :=
        two_step P (W P ⊓ Q.1) (W P) hin inf_le_left (hW_le P) ⟨v, Submodule.mem_inf.mpr ⟨hvP, hvQ⟩, hv⟩ (hW_ne P)
      have e2 : W P ⊓ Q.1 = Q.1 :=
        two_step P (W P ⊓ Q.1) Q.1 hin inf_le_right hQP ⟨v, Submodule.mem_inf.mpr ⟨hvP, hvQ⟩, hv⟩ hne2
      rw [← e1, e2]

  have core : ∀ (N' N : FullLattice 𝒪 K), N.1 ≤ M.1 → ¬ N.1 ≤ latticeMap (scalarGL u) M.1 →
      latticeMap (scalarGL u) N.1 ≤ N'.1 → N'.1 ≤ N.1 → W N ≤ N'.1 → W N' ≤ latticeMap (scalarGL u) N.1 →
      N.1 = M.1 ∨ N'.1 = latticeMap (scalarGL u) M.1 := by
    intro N' N hNM hN_not hN₁ hN₂ hN₃ hN₄
    by_cases hNM' : N.1 = M.1
    · exact Or.inl hNM'
    right
    obtain ⟨k, hk⟩ := exists_pow_smul_mem hπ N M
    have hkM : latticeMap (scalarGL (u ^ k)) M.1 ≤ N.1 := by
      rintro _ hx
      obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.1 hx
      rw [Units.val_pow_eq_pow_val, hu, ← map_pow]
      exact hk w hw

    have walk : ∀ (k : ℕ) (A : FullLattice 𝒪 K), N.1 ≤ A.1 → ¬ N.1 ≤ latticeMap (scalarGL u) A.1 →
        latticeMap (scalarGL (u ^ k)) A.1 ≤ N.1 → N.1 ≠ A.1 →
        W (P1 u N A) = latticeMap (scalarGL u) A.1 → N'.1 = latticeMap (scalarGL u) A.1 := by
      intro k
      induction k with
      | zero =>
        intro A h1 _ h3 h4 _
        exfalso
        apply h4
        rw [pow_zero, scalarGL_one, latticeMap_one] at h3
        exact le_antisymm h1 h3
      | succ k ih =>
        intro A hNA hNA_not hkA hNA_ne hWP
        have hNP_le : N.1 ≤ (P1 u N A).1 := le_sup_left
        have hPA : (P1 u N A).1 ≤ A.1 := sup_le hNA (sc_le u hu _)
        by_cases hNP : N.1 = (P1 u N A).1
        ·
          have hP : P1 u N A = N := (Subtype.ext hNP).symm
          rw [hP] at hWP
          symm
          refine two_step N (latticeMap (scalarGL u) A.1) N'.1 ?_ ?_ hN₂ ?_ (strict N' N hN₃ hN₄).1
          · intro v hv
            exact smul_mem_sc u hu (hNA hv)
          · rw [← hWP]
            exact hN₃
          · by_contra hcon
            push Not at hcon
            exact hNA_ne (le_antisymm hNA (le_of_latticeMap_le (scalarGL u) (fun v hv => hcon v hv)))
        ·
          exfalso
          have hscP_le : latticeMap (scalarGL u) (P1 u N A).1 ≤ latticeMap (scalarGL u) A.1 := by
            rw [P1_val, sc_sup]
            exact sup_le (latticeMap_mono _ hNA) (sc_le u hu _)
          have hN_not_P : ¬ N.1 ≤ latticeMap (scalarGL u) (P1 u N A).1 := fun h => hNA_not (h.trans hscP_le)
          have hkP : latticeMap (scalarGL (u ^ k)) (P1 u N A).1 ≤ N.1 := by
            rw [P1_val, sc_sup, sc_pow_one u A.1, sc_pow_pow]
            exact sup_le (sc_pow_le u hu k N.1) hkA
          have hedge1 : latticeMap (scalarGL u) (P1 u N A).1 ≠ (P1 u N (P1 u N A)).1 := by
            intro h
            apply hN_not_P
            rw [h]
            exact le_sup_left
          have hedge2 : (P1 u N (P1 u N A)).1 ≠ (P1 u N A).1 := by
            intro h
            apply hNP
            apply le_antisymm hNP_le
            refine sup_le le_rfl ?_
            have h1 : latticeMap (scalarGL u) A.1 ≤ N.1 ⊔ latticeMap (scalarGL u) (latticeMap (scalarGL u) A.1) := by
              have h0 : latticeMap (scalarGL u) A.1 ≤ (P1 u N (P1 u N A)).1 := by
                rw [h]
                exact le_sup_right
              refine h0.trans ?_
              rw [P1_val, P1_val, sc_sup]
              exact sup_le le_sup_left (sup_le ((sc_le u hu _).trans le_sup_left) le_sup_right)
            refine (absorb u hu N.1 _ h1 k).trans (sup_le le_rfl ?_)
            rw [sc_pow_one u A.1, sc_pow_one u (latticeMap (scalarGL (u ^ 1)) A.1), sc_pow_pow, sc_pow_pow]
            rw [show k + (1 + 1) = 1 + (k + 1) by omega]
            exact pow_le_of_pow_le u hu hkA 1
          have hWP₂ : W (P1 u N (P1 u N A)) = latticeMap (scalarGL u) (P1 u N A).1 := by
            rcases mono_lemma (P1 u N A) (P1 u N (P1 u N A)) le_sup_right
                (sup_le hNP_le (sc_le u hu _)) hedge1 hedge2 with h | h
            · exact h
            · exfalso
              apply hNA_not
              rw [hWP] at h
              rw [h]
              exact le_sup_left
          have hih := ih (P1 u N A) hNP_le hN_not_P hkP hNP hWP₂
          have hN'eq : N' = FullLattice.act (scalarGL u) (P1 u N A) := Subtype.ext hih
          have hWN' : W N' = latticeMap (scalarGL u) (latticeMap (scalarGL u) A.1) := by
            rw [hN'eq, hW_hom, hWP]
          apply hNP
          apply le_antisymm hNP_le (sup_le le_rfl ?_)
          apply le_of_latticeMap_le (scalarGL u)
          rw [← hWN']
          exact hN₄

    have hMne : M'.1 ≠ M.1 ∧ latticeMap (scalarGL u) M.1 ≠ M'.1 := strict M' M hM₃ hM₄
    have hWM : W M = M'.1 := two_step M (W M) M'.1 (hπW M) hM₃ hM₂ (hW_ex M) hMne.1
    have hP1_ne1 : latticeMap (scalarGL u) M.1 ≠ (P1 u N M).1 := by
      intro h
      apply hN_not
      rw [h]
      exact le_sup_left
    have hP1_ne2 : (P1 u N M).1 ≠ M.1 := by
      intro h
      apply hNM'
      apply le_antisymm hNM
      have h1 : M.1 ≤ N.1 ⊔ latticeMap (scalarGL u) M.1 := by
        rw [← P1_val, h]
      refine (absorb u hu N.1 M.1 h1 k).trans (sup_le le_rfl ?_)
      rw [sc_pow_one u M.1, sc_pow_pow]
      rw [show k + 1 = 1 + k by omega]
      exact pow_le_of_pow_le u hu hkM 1
    have hWP1 : W (P1 u N M) = latticeMap (scalarGL u) M.1 := by
      rcases mono_lemma M (P1 u N M) le_sup_right (sup_le hNM (sc_le u hu _)) hP1_ne1 hP1_ne2 with h | h
      · exact h
      · have hM'P : M' = P1 u N M := Subtype.ext (hWM ▸ h)
        refine two_step (P1 u N M) _ _ (hπW _) ?_ le_sup_right (hW_ex _) hP1_ne1
        rw [← hM'P]
        exact hM₄
    exact walk k M hNM hN_not hkM hNM' hWP1

  obtain ⟨c, hcL, v₀, hv₀L, hv₀⟩ := exists_unit_normalize hπ L M
  have hLcM : (FullLattice.act (scalarGL c) L).1 ≤ M.1 := by
    rintro _ hx
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.1 hx
    exact hcL w hw
  have hLc_not : ¬ (FullLattice.act (scalarGL c) L).1 ≤ latticeMap (scalarGL u) M.1 := by
    intro h
    apply hv₀
    have hm : (c : K) • v₀ ∈ latticeMap (scalarGL u) M.1 := h (mem_latticeMap_scalarGL.2 ⟨v₀, hv₀L, rfl⟩)
    obtain ⟨w, hw, hw'⟩ := mem_latticeMap_scalarGL.1 hm
    exact ⟨w, hw, by rw [← hw', hu]⟩
  have hL₁' : latticeMap (scalarGL u) (FullLattice.act (scalarGL c) L).1 ≤ (FullLattice.act (scalarGL c) L').1 := by
    show latticeMap (scalarGL u) (latticeMap (scalarGL c) L.1) ≤ latticeMap (scalarGL c) L'.1
    rw [sc_comm]
    exact latticeMap_mono _ hL₁
  have hL₂' : (FullLattice.act (scalarGL c) L').1 ≤ (FullLattice.act (scalarGL c) L).1 := latticeMap_mono _ hL₂
  have hL₃' : W (FullLattice.act (scalarGL c) L) ≤ (FullLattice.act (scalarGL c) L').1 := by
    rw [hW_hom]
    exact latticeMap_mono _ hL₃
  have hL₄' : W (FullLattice.act (scalarGL c) L') ≤ latticeMap (scalarGL u) (FullLattice.act (scalarGL c) L).1 := by
    rw [hW_hom]
    show latticeMap (scalarGL c) (W L') ≤ latticeMap (scalarGL u) (latticeMap (scalarGL c) L.1)
    rw [sc_comm u c]
    exact latticeMap_mono _ hL₄
  rcases core _ _ hLcM hLc_not hL₁' hL₂' hL₃' hL₄' with h | h
  · refine ⟨c⁻¹, M, L, Or.inr rfl, Or.inr rfl, ?_⟩
    change latticeMap (scalarGL c) L.1 = M.1 at h
    rw [← h, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]
  · refine ⟨c⁻¹ * u, M, L', Or.inr rfl, Or.inl rfl, ?_⟩
    change latticeMap (scalarGL c) L'.1 = latticeMap (scalarGL u) M.1 at h
    rw [scalarGL_mul, latticeMap_mul, ← h, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one,
      latticeMap_one]

end ShareVertex

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) [𝔭.IsPrime] (h𝔭 : algebraMap 𝒪 B π ∈ 𝔭)
    (M' M L' L : FullLattice 𝒪 K) (hM : d.EdgeNondegAt π 𝔭 M' M) (hL : d.EdgeNondegAt π 𝔭 L' L) :
    ∃ (c : Kˣ) (X Y : FullLattice 𝒪 K), (X = M' ∨ X = M) ∧ (Y = L' ∨ Y = L) ∧
      latticeMap (scalarGL c) X.1 = Y.1 := by
  classical
  by_cases hVex : ∃ P : FullLattice 𝒪 K, d.VertexNondegAt π 𝔭 P
  · obtain ⟨P, hP⟩ := hVex
    obtain ⟨c, hc⟩ :=
      CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
        hπ d 𝔭 h𝔭 P M' M hP hM
    obtain ⟨c', hc'⟩ :=
      CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
        hπ d 𝔭 h𝔭 P L' L hP hL
    refine ⟨c' * c⁻¹, ?_⟩
    rcases hc with hX | hX <;> rcases hc' with hY | hY
    · exact ⟨M', L', Or.inl rfl, Or.inl rfl, ShareVertex.latticeMap_scalarGL_of_eq_of_eq hX hY⟩
    · exact ⟨M', L, Or.inl rfl, Or.inr rfl, ShareVertex.latticeMap_scalarGL_of_eq_of_eq hX hY⟩
    · exact ⟨M, L', Or.inr rfl, Or.inl rfl, ShareVertex.latticeMap_scalarGL_of_eq_of_eq hX hY⟩
    · exact ⟨M, L, Or.inr rfl, Or.inr rfl, ShareVertex.latticeMap_scalarGL_of_eq_of_eq hX hY⟩
  · push Not at hVex
    obtain ⟨hM₁, hM₂, hM₃, hM₄⟩ := ShareVertex.edge_read hπ d 𝔭 M' M hM
    obtain ⟨hL₁, hL₂, hL₃, hL₄⟩ := ShareVertex.edge_read hπ d 𝔭 L' L hL
    exact ShareVertex.lattice_walk hπ (ShareVertex.W d 𝔭) (ShareVertex.W_le d 𝔭) (ShareVertex.W_ne d 𝔭)
      (ShareVertex.pi_smul_mem_W d 𝔭 h𝔭) (fun A => ShareVertex.not_W_le_of_not_vertexNondegAt hπ d 𝔭 A (hVex A))
      (ShareVertex.W_mono d 𝔭) (ShareVertex.W_act_scalarGL d 𝔭) M' M L' L hM₁ hM₂ hM₃ hM₄ hL₁ hL₂ hL₃ hL₄

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt (solution)
