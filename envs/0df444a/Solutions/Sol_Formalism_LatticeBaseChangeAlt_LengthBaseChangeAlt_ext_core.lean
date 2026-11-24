-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt.ext_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:17.816278+00:00
-- url     : https://prove2.me/submissions/45ba8b7a-464b-4027-962f-5732eab0c82e

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_le_of_map
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_lattice_span_of_basis
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_len_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module TensorProduct
open Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt
open BQuot
variable {O K K₁ V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁]
  [Algebra.IsSeparable K K₁] [Algebra O K₁] [IsScalarTower O K K₁]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
namespace Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt
theorem _root_.solution (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) (c : V →ₗ[K] (Fin n → K₁))
    (N : Submodule K V) (hN : LinearMap.ker c ≤ N) (th : Fin n → V)
    (hspan : LinearMap.ker c ⊔ Submodule.span K (Set.range th) = ⊤)
    (X : Submodule O V) (e be : ℕ)
    (hX : ∀ x ∈ X, ∀ i, ∃ y ∈ integralClosure O K₁,
        c x i = (algebraMap O K₁ ϖ) ^ ((e : ℤ) - (be : ℤ)) * y)
    (hth : ∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X)
    (a a' : O) (ha : a ≠ 0)
    (hdet : algebraMap O K a =
      Algebra.norm K (Matrix.of fun i j => c (th j) i).det * algebraMap O K a') :
    (finrank K K₁ : ℕ∞) * ql X ((X ⊓ N.restrictScalars O) ⊔
        Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)) +
      IsDiscreteValuationRing.addVal O a' ≤
      IsDiscreteValuationRing.addVal O a + ((finrank K K₁ * n * be : ℕ) : ℕ∞) := by
  classical
  set p : K := algebraMap O K ϖ with hp
  have hp0 : p ≠ 0 := by
    rw [hp]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  have hP1 : algebraMap O K₁ ϖ = algebraMap K K₁ p := IsScalarTower.algebraMap_apply O K K₁ ϖ
  set d := finrank K K₁ with hd
  set C : Matrix (Fin n) (Fin n) K₁ := Matrix.of fun i j => c (th j) i with hC
  have hNC0 : Algebra.norm K C.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact ha ((map_eq_zero_iff _ (IsFractionRing.injective O K)).1 hdet)
  have hC0 : C.det ≠ 0 := by
    intro h0
    exact hNC0 (by rw [h0, Algebra.norm_zero])
  set Tj : Submodule O V := Submodule.span O (Set.range fun j => p ^ e • th j) with hTj
  have hTX : Tj ≤ X := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hth j)

  let g : (Fin n → K) →ₗ[K] (Fin n → K₁) := c ∘ₗ Fintype.linearCombination K th
  have hg : ∀ x i, g x i = ∑ j, C i j * algebraMap K K₁ (x j) := by
    intro x i
    show c (Fintype.linearCombination K th x) i = _
    rw [Fintype.linearCombination_apply, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Pi.smul_apply, Algebra.smul_def, mul_comm]
    rfl
  have hgs : ∀ j, g (Pi.single j 1) = c (th j) := by
    intro j
    show c (Fintype.linearCombination K th (Pi.single j 1)) = _
    rw [Fintype.linearCombination_apply_single, one_smul]
  have hginj : LinearMap.ker g = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : C.mulVec (fun j => algebraMap K K₁ (x j)) = 0 := by
      funext i
      have := congrFun hx i
      rw [hg] at this
      exact this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hC0 h1
    funext j
    exact (map_eq_zero_iff _ (algebraMap K K₁).injective).1 (congrFun h2 j)
  have hrange : ∀ v, ∃ x, c v = g x := by
    intro v
    have hv : v ∈ LinearMap.ker c ⊔ Submodule.span K (Set.range th) := by rw [hspan]; trivial
    obtain ⟨k, hk, s, hs, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hs
    refine ⟨x, ?_⟩
    rw [map_add, LinearMap.mem_ker.1 hk, zero_add]
    show _ = c (Fintype.linearCombination K th x)
    rw [Fintype.linearCombination_apply]
  obtain ⟨r, hr⟩ := g.exists_leftInverse_of_injective hginj
  have hr' : ∀ x, r (g x) = x := fun x => LinearMap.congr_fun hr x
  let q : K := p ^ ((be : ℤ) - (e : ℤ))
  have hq0 : q ≠ 0 := zpow_ne_zero _ hp0
  let F : V →ₗ[O] (Fin n → K) := (r ∘ₗ (q • c)).restrictScalars O
  have hF : ∀ v, F v = r (q • c v) := fun v => rfl
  have hgF : ∀ v, g (F v) = q • c v := by
    intro v
    obtain ⟨x, hx⟩ := hrange v
    rw [hF, hx, ← map_smul, hr']
  let w : Fin n → (Fin n → K) := fun j => F (p ^ e • th j)
  have hw' : ∀ j, w j = p ^ be • Pi.single j 1 := by
    intro j
    show F (p ^ e • th j) = _
    rw [hF, c.map_smul, smul_smul, ← zpow_natCast p e, ← zpow_add₀ hp0, sub_add_cancel,
      zpow_natCast, ← hgs, ← map_smul, hr']

  let I1 : Submodule O K₁ := (integralClosure O K₁).toSubmodule
  have hI1 : IsNoetherian O ↥I1 := IsIntegralClosure.isNoetherian O K K₁ (integralClosure O K₁)
  let L : Submodule O (Fin n → K) :=
    (Submodule.pi Set.univ fun _ => I1).comap (g.restrictScalars O)
  have hL : ∀ x, x ∈ L ↔ ∀ i, g x i ∈ I1 := by
    intro x
    simp [L, Submodule.mem_pi]
  have hFX : ∀ x ∈ X, F x ∈ L := by
    intro x hx
    rw [hL]
    intro i
    obtain ⟨y, hy, hxy⟩ := hX x hx i
    rw [hgF, Pi.smul_apply, hxy, Algebra.smul_def, hP1, ← mul_assoc, map_zpow₀,
      ← zpow_add₀ ((map_ne_zero _).2 hp0)]
    have h5 : (be : ℤ) - (e : ℤ) + ((e : ℤ) - (be : ℤ)) = 0 := by ring
    rw [h5, zpow_zero, one_mul]
    exact hy
  have hwL : ∀ j, w j ∈ L := fun j => hFX _ (hth j)
  have hLfg : L.FG := by
    let φ : ↥L →ₗ[O] (Fin n → ↥I1) := LinearMap.pi fun i =>
      LinearMap.codRestrict I1 (LinearMap.proj i ∘ₗ g.restrictScalars O ∘ₗ L.subtype)
        (fun x => (hL x).1 x.2 i)
    have hφ : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      apply LinearMap.ker_eq_bot.1 hginj
      funext i
      exact congrArg Subtype.val (congrFun hxy i)
    have : IsNoetherian O ↥L := isNoetherian_of_injective φ hφ
    exact (Submodule.fg_top L).1 (Module.Finite.fg_top)
  have hLspan : Submodule.span K (L : Set (Fin n → K)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : (Pi.basisFun K (Fin n)) j = (p ^ be)⁻¹ • w j := by
      rw [hw', smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_smul, Pi.basisFun_apply]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hwL j))
  obtain ⟨b0, hb0⟩ := Formalism.LatticeIndexTer.LatticeIndexDeterminant.lattice_span_of_basis O K (Fin n → K) L ⟨hLfg, hLspan⟩
  let b : Basis (Fin n) K (Fin n → K) := b0.reindex (finCongr (by simp))
  have hb : L = Submodule.span O (Set.range b) := by
    rw [hb0, Basis.range_reindex]
  let bf := Pi.basisFun K (Fin n)
  let B : Matrix (Fin n) (Fin n) K := bf.toMatrix b
  have hmat : b.toMatrix w = p ^ be • b.toMatrix bf := by
    ext i j
    rw [Basis.toMatrix_apply, hw', map_smul]
    simp [bf, Basis.toMatrix_apply]
  have hBB : (b.toMatrix bf).det * B.det = 1 := by
    rw [← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  have hdw : (b.toMatrix w).det = (p ^ be) ^ n * (b.toMatrix bf).det := by
    rw [hmat, Matrix.det_smul, Fintype.card_fin]
  have hdw0 : (b.toMatrix w).det ≠ 0 := by
    rw [hdw]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hp0)) (left_ne_zero_of_mul_eq_one hBB)
  obtain ⟨e0, he0, hlen⟩ := Formalism.LatticeIndexTer.LatticeIndexDeterminant.len_span (O := O) b w
    (fun j => hb ▸ hwL j) hdw0
  have hle : ql X ((X ⊓ N.restrictScalars O) ⊔ Tj) ≤ IsDiscreteValuationRing.addVal O e0 := by
    rw [← hlen]
    refine ql_le_of_map (F ∘ₗ X.subtype) (fun x => hb ▸ hFX _ x.2) ?_
    intro x hx
    have hx' : F (x : V) ∈ Submodule.span O (Set.range w) := hx
    have hmap : Submodule.span O (Set.range w) = Tj.map F := by
      rw [hTj, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap] at hx'
    obtain ⟨t, ht, htx⟩ := hx'
    have hker : (x : V) - t ∈ LinearMap.ker c := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      have h3 := congrArg g htx
      rw [hgF, hgF] at h3
      exact (smul_right_injective _ hq0 h3).symm
    have : (x : V) = ((x : V) - t) + t := by abel
    rw [this]
    exact Submodule.add_mem_sup ⟨X.sub_mem x.2 (hTX ht), hN hker⟩ ht

  let Λ : Matrix (Fin n) (Fin n) K₁ := Matrix.of fun i j => g (b j) i
  have hΛ : Λ = C * (algebraMap K K₁).mapMatrix B := by
    ext i j
    rw [Matrix.mul_apply]
    show g (b j) i = _
    rw [hg]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [B, bf, Basis.toMatrix_apply]
  have hΛdet : Λ.det = C.det * algebraMap K K₁ B.det := by
    rw [hΛ, Matrix.det_mul, RingHom.map_det]
  have hΛint : IsIntegral O Λ.det := by
    apply IsIntegral.det
    intro i j
    have : b j ∈ L := by
      rw [hb]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact (hL _).1 this i
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm K hΛint)
  have hs' : algebraMap O K s = Algebra.norm K C.det * B.det ^ d := by
    rw [hs, hΛdet, map_mul, Algebra.norm_algebraMap]
  have hrel : e0 ^ d * s * a' = ϖ ^ (d * n * be) * a := by
    apply IsFractionRing.injective O K
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, he0, hdw, hs', hdet, ← hp]
    have : ((p ^ be) ^ n * (b.toMatrix bf).det) ^ d * (Algebra.norm K C.det * B.det ^ d) =
        ((p ^ be) ^ n) ^ d * ((b.toMatrix bf).det * B.det) ^ d * Algebra.norm K C.det := by ring
    rw [this, hBB, one_pow, mul_one, ← pow_mul, ← pow_mul]
    have h4 : be * (n * d) = d * n * be := by ring
    rw [h4]
    ring
  have hval : (d : ℕ∞) * IsDiscreteValuationRing.addVal O e0 + IsDiscreteValuationRing.addVal O s +
      IsDiscreteValuationRing.addVal O a' =
      IsDiscreteValuationRing.addVal O a + ((d * n * be : ℕ) : ℕ∞) := by
    have := congrArg (IsDiscreteValuationRing.addVal O) hrel
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ] at this
    rw [add_comm (IsDiscreteValuationRing.addVal O a)]
    simpa using this
  rw [← hval]
  calc (d : ℕ∞) * ql X ((X ⊓ N.restrictScalars O) ⊔ Tj) + IsDiscreteValuationRing.addVal O a'
      ≤ (d : ℕ∞) * IsDiscreteValuationRing.addVal O e0 + IsDiscreteValuationRing.addVal O a' :=
        add_le_add (mul_le_mul_right hle _) le_rfl
    _ ≤ _ := add_le_add le_self_add le_rfl
end Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt
