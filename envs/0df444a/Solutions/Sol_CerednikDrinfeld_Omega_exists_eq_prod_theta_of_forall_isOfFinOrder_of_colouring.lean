-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bcd945cc-707f-53aa-ae07-58b3adbe812a

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq
import Theorems.Thm_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq
import Theorems.Thm_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_div_sub_one_lt
import Theorems.Thm_CerednikDrinfeld_Omega_exists_points_prod_theta_eq_of_v_sub_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace JC4

theorem forall_append {α : Type} {m n : ℕ} {P : α → Prop} {u : Fin m → α} {v : Fin n → α}
    (hu : ∀ i, P (u i)) (hv : ∀ i, P (v i)) : ∀ i, P (Fin.append u v i) := by
  intro i
  refine Fin.addCases (motive := fun i => P (Fin.append u v i)) (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using hu j
  · simpa only [Fin.append_right] using hv j

theorem exists_mem_upperHalfPlane
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    ∃ z₀ : K, z₀ ∈ upperHalfPlane K₀ K := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K₀ K (algebraMap R K₀ ϖ)) (by norm_num : 0 < 2)
  refine ⟨x, ?_⟩
  rw [mem_upperHalfPlane_iff]
  intro a ha

  have hvx : Valued.v x ≤ 1 := by
    by_contra h
    have h1 : 1 < Valued.v x := not_le.mp h
    have : (1 : Γ₀) < Valued.v x ^ 2 := by
      calc (1 : Γ₀) < Valued.v x := h1
        _ = Valued.v x * 1 := (mul_one _).symm
        _ ≤ Valued.v x * Valued.v x := mul_le_mul_right h1.le _
        _ = Valued.v x ^ 2 := (pow_two _).symm
    rw [← map_pow, hx] at this
    exact absurd (hint ϖ) (not_le.mpr this)
  rw [← ha] at hvx
  obtain ⟨r, hr⟩ := hv a hvx

  have hK : algebraMap K₀ K (algebraMap R K₀ (r * r)) = algebraMap K₀ K (algebraMap R K₀ ϖ) := by
    rw [← hx, ← ha, map_mul, map_mul, hr, pow_two]
  have hrr : r * r = ϖ :=
    IsFractionRing.injective R K₀ ((algebraMap K₀ K).injective hK)
  rcases hϖ.isUnit_or_isUnit hrr.symm with hu | hu <;>
    exact hϖ.not_isUnit (hrr ▸ hu.mul hu)

end JC4

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) [IsDomain ↥(holRing ϖ₁)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1)

    (χ : G →* Kˣ) (hχ : ∀ γ : G, IsOfFinOrder γ → χ γ = 1) :
    ∃ (n : ℕ) (a b : Fin n → K) (z₀ : K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧ z₀ ∈ upperHalfPlane K₀ K ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      ∀ β : G, ((χ β : Kˣ) : K) = ∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀) := by
  classical

  have hst : {γ : G | ρ γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀}.Finite := by
    haveI := hfin (LT.LatticeTree.stdVertex R K₀)
    have hset : {γ : G | ρ γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀} =
        ((MulAction.stabilizer G (LT.LatticeTree.stdVertex R K₀) : Subgroup G) : Set G) := by
      ext γ
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff, hρ γ]
    rw [hset]
    exact Set.toFinite _
  have hdisc : IsDiscrete K ρ :=
    CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ hst

  obtain ⟨z₀, hz₀⟩ := JC4.exists_mem_upperHalfPlane R K₀ ϖ hϖ K hint hv

  have key : ∀ (n : ℕ) (a b : Fin n → K), (∀ i, a i ∈ upperHalfPlane K₀ K) → (∀ i, b i ∈ upperHalfPlane K₀ K) →
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) → (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) →
      ∃ c : G →* Kˣ, (∀ β : G, ((c β : Kˣ) : K) = ∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) ∧
        ∀ γ : G, IsOfFinOrder γ → c γ = 1 := by
    intro n a b ha hb hza hzb
    have hci : ∀ i : Fin n, ∃ c : G →* Kˣ, ∀ β : G, ((c β : Kˣ) : K) = theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀) := by
      intro i
      obtain ⟨c, hc, -⟩ := CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq K₀ K ϖ₁ hex ρ hdisc
        (ha i) (hb i) hz₀ (hza i) (hzb i)
      exact ⟨c, hc⟩
    choose c hc using hci
    refine ⟨∏ i, c i, fun β => ?_, fun γ hγ => ?_⟩
    · rw [MonoidHom.finsetProd_apply, Units.coe_prod]
      exact Finset.prod_congr rfl fun i _ => hc i β
    · rw [MonoidHom.finsetProd_apply]
      refine Finset.prod_eq_one fun i _ => ?_
      apply Units.val_eq_one.mp
      rw [hc i γ]
      exact CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder K₀ K ϖ₁ hex ρ hdisc
        (ha i) (hb i) hz₀ (hza i) (hzb i) γ hγ

  obtain ⟨n₁, a₁, b₁, ha₁, hb₁, hza₁, hzb₁, hv₁⟩ :=
    CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex ρ hρ hfin τ hτ hadj htame z₀ hz₀ χ
  obtain ⟨c₁, hc₁, hc₁t⟩ := key n₁ a₁ b₁ ha₁ hb₁ hza₁ hzb₁

  set η : G →* Kˣ := χ * c₁⁻¹ with hηdef
  have hηβ : ∀ β : G, ((η β : Kˣ) : K) = ((χ β : Kˣ) : K) * (((c₁ β : Kˣ) : K))⁻¹ := by
    intro β
    simp only [hηdef, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  have hη₁ : ∀ β : G, Valued.v ((η β : Kˣ) : K) = 1 := by
    intro β
    have hne : Valued.v ((χ β : Kˣ) : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr (χ β).ne_zero
    rw [hηβ, map_mul, map_inv₀, hc₁ β, hv₁ β, mul_inv_cancel₀ hne]
  have hηt : ∀ γ : G, IsOfFinOrder γ → η γ = 1 := by
    intro γ hγ
    simp only [hηdef, MonoidHom.mul_apply, MonoidHom.inv_apply, hχ γ hγ, hc₁t γ hγ, inv_one, mul_one]
  obtain ⟨n₂, a₂, b₂, ha₂, hb₂, hza₂, hzb₂, hv₂⟩ :=
    CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_div_sub_one_lt R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex ρ hρ hfin
      τ hτ hadj htame z₀ hz₀ η hη₁ hηt
  obtain ⟨c₂, hc₂, hc₂t⟩ := key n₂ a₂ b₂ ha₂ hb₂ hza₂ hzb₂

  set θ : G →* Kˣ := η * c₂⁻¹ with hθdef
  have hθβ : ∀ β : G, ((θ β : Kˣ) : K) = ((η β : Kˣ) : K) * (((c₂ β : Kˣ) : K))⁻¹ := by
    intro β
    simp only [hθdef, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  have hθ₁ : ∀ β : G, Valued.v (((θ β : Kˣ) : K) - 1) < 1 := by
    intro β
    have h := (hv₂ β).2
    rw [← hc₂ β, div_eq_mul_inv] at h
    rwa [hθβ]
  have hθt : ∀ γ : G, IsOfFinOrder γ → θ γ = 1 := by
    intro γ hγ
    simp only [hθdef, MonoidHom.mul_apply, MonoidHom.inv_apply, hηt γ hγ, hc₂t γ hγ, inv_one, mul_one]
  obtain ⟨n₃, a₃, b₃, ha₃, hb₃, hza₃, hzb₃, h₃⟩ :=
    CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex ρ hρ hfin
      τ hτ hadj htame z₀ hz₀ θ hθ₁ hθt

  refine ⟨n₁ + n₂ + n₃, Fin.append (Fin.append a₁ a₂) a₃, Fin.append (Fin.append b₁ b₂) b₃, z₀,
    JC4.forall_append (JC4.forall_append ha₁ ha₂) ha₃, JC4.forall_append (JC4.forall_append hb₁ hb₂) hb₃, hz₀,
    JC4.forall_append (P := fun x => ∀ γ : G, pmoebius K₀ (ρ γ) x ≠ z₀)
      (JC4.forall_append (P := fun x => ∀ γ : G, pmoebius K₀ (ρ γ) x ≠ z₀) hza₁ hza₂) hza₃,
    JC4.forall_append (P := fun x => ∀ γ : G, pmoebius K₀ (ρ γ) x ≠ z₀)
      (JC4.forall_append (P := fun x => ∀ γ : G, pmoebius K₀ (ρ γ) x ≠ z₀) hzb₁ hzb₂) hzb₃,
    fun β => ?_⟩
  have hsplit : ∏ i, theta ρ (Fin.append (Fin.append a₁ a₂) a₃ i) (Fin.append (Fin.append b₁ b₂) b₃ i) z₀
        (pmoebius K₀ (ρ β) z₀) =
      ((∏ i, theta ρ (a₁ i) (b₁ i) z₀ (pmoebius K₀ (ρ β) z₀)) * ∏ i, theta ρ (a₂ i) (b₂ i) z₀ (pmoebius K₀ (ρ β) z₀)) *
        ∏ i, theta ρ (a₃ i) (b₃ i) z₀ (pmoebius K₀ (ρ β) z₀) := by
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hsplit, ← hc₁ β, ← hc₂ β, ← h₃ β, hθβ, hηβ]
  have h1 : ((c₁ β : Kˣ) : K) ≠ 0 := (c₁ β).ne_zero
  have h2 : ((c₂ β : Kˣ) : K) ≠ 0 := (c₂ β).ne_zero
  field_simp

end S_CerednikDrinfeld_Omega_exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring (solution)
