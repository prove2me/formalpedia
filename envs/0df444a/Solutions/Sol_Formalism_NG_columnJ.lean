-- Prove2me | solution 1 for Formalism.NG.columnJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:09:57.364068+00:00
-- url     : https://prove2.me/submissions/e205a624-2c6a-4f52-bc47-70173150774f

import Definitions.Def_Formalism_CharacterColumnKernels_StatGlobalModule
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.NG
open Module
private theorem place_kernel {A T' K V G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [SMulCommClass A K V] [FiniteDimensional K V]
    (r : G →* A) (χ : G →* T'ˣ) (D : Subgroup G) (j : ℕ) (Kc : Fin j → G → A) (k0 : G → A)
    (s1 η : V) (L : Submodule K (D → V))
    (hB : LinearMap.range (colD (K := K) (V := V) r χ D) ≤ L)
    (hK : ∀ a, (fun g : D => Kc a g • s1) ∈ L) (hk : (fun g : D => k0 g • η) ∈ L)
    (hQ : Module.rank K (L ⧸ (LinearMap.range (colD (K := K) (V := V) r χ D)).comap L.subtype) ≤
        (j + Module.finrank K (LinearMap.ker (colD (K := K) (V := V) r χ D)) : ℕ)) :
    ∃ p : V × (Fin j → K) × K, p ≠ 0 ∧ ∀ g ∈ D,
      ∑ a, p.2.1 a • (Kc a g • s1) + p.2.2 • (k0 g • η) =
        ((((χ g)⁻¹ : T'ˣ) : T') • r g) • p.1 - p.1 := by
  classical
  by_cases hker : LinearMap.ker (colD (K := K) (V := V) r χ D) = ⊥
  · have hfin : Module.finrank K (LinearMap.ker (colD (K := K) (V := V) r χ D)) = 0 := by
      rw [hker]; simp
    rw [hfin] at hQ
    let ψ : ((Fin j → K) × K) →ₗ[K] (D → V) :=
      { toFun := fun x => ∑ a, x.1 a • (fun g : D => Kc a g • s1) + x.2 • (fun g : D => k0 g • η)
        map_add' := fun x y => by
          simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
          abel
        map_smul' := fun c x => by
          simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
            RingHom.id_apply, smul_add, Finset.smul_sum] }
    have hψ : ∀ x, ψ x ∈ L := fun x =>
      L.add_mem (L.sum_mem fun a _ => L.smul_mem _ (hK a)) (L.smul_mem _ hk)
    let π := ((LinearMap.range (colD (K := K) (V := V) r χ D)).comap L.subtype).mkQ ∘ₗ
      LinearMap.codRestrict L ψ hψ
    have hnot : ¬ Function.Injective π := by
      intro hinj
      have h1 : Module.finrank K (LinearMap.range π) = j + 1 := by
        rw [LinearMap.finrank_range_of_inj hinj]; simp
      have h2 : Module.rank K (LinearMap.range π) ≤ _ := Submodule.rank_le (LinearMap.range π)
      rw [← Module.finrank_eq_rank, h1] at h2
      have h3 : j + 1 ≤ j + 0 := by exact_mod_cast h2.trans hQ
      omega
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (fun h => hnot (LinearMap.ker_eq_bot.1 h))
    have hx' : LinearMap.codRestrict L ψ hψ x ∈
        (LinearMap.range (colD (K := K) (V := V) r χ D)).comap L.subtype := by
      rw [← Submodule.Quotient.mk_eq_zero]; exact LinearMap.mem_ker.1 hx
    obtain ⟨v, hv⟩ : ψ x ∈ LinearMap.range (colD (K := K) (V := V) r χ D) := hx'
    refine ⟨(v, x.1, x.2), fun h => hx0 (Prod.ext (congrArg (fun p => p.2.1) h)
      (congrArg (fun p => p.2.2) h)), fun g hg => ?_⟩
    have e1 : ψ x ⟨g, hg⟩ = ∑ a, x.1 a • (Kc a g • s1) + x.2 • (k0 g • η) := by
      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    rw [← e1, ← hv]
    rfl
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hker
    refine ⟨(v, 0, 0), fun h => hv0 (congrArg Prod.fst h), fun g hg => ?_⟩
    have h := congrFun (LinearMap.mem_ker.1 hv) ⟨g, hg⟩
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    exact h.symm
section Hom
variable {A T' K V G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [Module T' V] [IsScalarTower T' A V]
    {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [Fintype ι] [DecidableEq ι] {j : ι → ℕ}
private theorem colFreeMap_colGen (φY : Ymod r χ E →ₗ[A] V) (n : ι → V) (s : (l : ι) → Fin (j l) → V) (s0 : ι → V)
    (y : Ymod r χ E) (l : ι) (c : A) (sv : Fin (j l) → A) (c₀ : A) :
    colFreeMap φY n s s0 (colGenJ y l c sv c₀) =
      φY y + (c • n l + ∑ a, sv a • s l a + c₀ • s0 l) := by
  rw [colGenJ]
  simp only [colFreeMap, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ l) h
private theorem colHom_exists (e₁ : A) (δ : T') (D : ι → Subgroup G) (Kc : ∀ l, Fin (j l) → G → A)
    (k0 : ι → G → A) (δx : K) (hδ : ∀ v : V, δ • v = δx • v)
    (φY : Ymod r χ E →ₗ[A] V) (n : ι → V) (s : (l : ι) → Fin (j l) → V) (s0 : ι → V)
    (h1 : ∀ l, E • n l = 0) (h2 : ∀ l a, e₁ • s l a = s l a)
    (h3 : ∀ l, E • s0 l = δx • s0 l)
    (h4 : ∀ l, ∀ g ∈ D l, φY ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ +
      ((((χ g)⁻¹ : T'ˣ) : T') • r g) • n l - n l =
        δx • (∑ a, Kc l a g • s l a + k0 l g • s0 l)) :
    ∃ φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] V, ∀ x : ColFreeJ A r χ E ι j,
      φ (Submodule.Quotient.mk x) = colFreeMap φY n s s0 x := by
  refine ⟨(colRelJ r χ E e₁ δ D j Kc k0).liftQ (colFreeMap φY n s s0) ?_, fun x => rfl⟩
  unfold colRelJ
  rw [Submodule.span_le]
  refine Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_
  · rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]
    simp [h1]
  · rintro _ ⟨l, a, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]
    simp [Pi.single_apply, ite_smul, sub_smul, h2]
  · rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]
    simp [algebraMap_smul, sub_smul, hδ, h3]
  · rintro _ ⟨l, g, hg, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]
    have key := h4 l g hg
    rw [smul_add, Finset.smul_sum, ← sub_eq_zero] at key
    simp only [neg_smul, mul_smul, algebraMap_smul, hδ, sub_smul, one_smul, Finset.sum_neg_distrib]
    rw [← key]
    abel
end Hom
end Formalism.NG
end

set_option autoImplicit false
open Formalism Formalism.NG
open Module
namespace Formalism.NG
theorem _root_.solution : StatColumnJ := by
  intro A T' K V G _ _ _ _ _ _ _ _ _ _ _ _ r χ E e₁ δ ι _ _ D j Kc k0 hE he₁ δx hδx hδ hrE hre₁
    hfix hL

  obtain ⟨xη, hxη⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (hrE ▸ Nat.one_pos)
  obtain ⟨x1, hx1⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (hre₁ ▸ Nat.one_pos)
  have hspan := (finrank_eq_one_iff_of_nonzero' xη hxη).mp hrE
  set η : V := (xη : V) with hηdef
  set s1 : V := (x1 : V) with hs1def
  have hηmem : η ∈ LinearMap.range (DistribSMul.toLinearMap K V E) := xη.2
  have hs1mem : s1 ∈ LinearMap.range (DistribSMul.toLinearMap K V e₁) := x1.2
  have hη0 : η ≠ 0 := fun h => hxη (Subtype.ext h)
  have hs10 : s1 ≠ 0 := fun h => hx1 (Subtype.ext h)
  obtain ⟨w0, hw0⟩ := hηmem
  obtain ⟨w1, hw1⟩ := hs1mem
  rw [DistribSMul.toLinearMap_apply] at hw0 hw1
  have hδA : ∀ w : V, algebraMap T' A δ • w = δx • w := by
    intro w; rw [algebraMap_smul, hδ]
  have hEη : E • η = δx • η := by
    rw [← hw0, smul_smul, hE, mul_smul, hδA]
  have he₁s1 : e₁ • s1 = s1 := by
    rw [← hw1, smul_smul, he₁]

  have hplace : ∀ l, ∃ p : V × (Fin (j l) → K) × K,
      (∀ g ∈ D l, ∑ a, p.2.1 a • (Kc l a g • s1) + p.2.2 • (k0 l g • η) =
        ((((χ g)⁻¹ : T'ˣ) : T') • r g) • p.1 - p.1) ∧
      ((E • p.1 = 0 ∧ p ≠ 0) ∨ E • p.1 = η) := by
    intro l
    obtain ⟨L, hB, hK, hk, hQ⟩ := hL l
    obtain ⟨p, hp0, hp⟩ := place_kernel r χ (D l) (j l) (Kc l) (k0 l) s1 η L hB
      (fun a => hK a s1 x1.2)
      (hk η xη.2) hQ
    by_cases hE0 : E • p.1 = 0
    · exact ⟨p, hp, Or.inl ⟨hE0, hp0⟩⟩
    · obtain ⟨t, ht⟩ := hspan ⟨E • p.1, p.1, rfl⟩
      have ht' : t • η = E • p.1 := congrArg Subtype.val ht
      have ht0 : t ≠ 0 := by
        rintro rfl; rw [zero_smul] at ht'; exact hE0 ht'.symm
      refine ⟨t⁻¹ • p, ?_, Or.inr ?_⟩
      · intro g hg
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
          ← Finset.smul_sum, ← smul_add, hp g hg, smul_sub, smul_comm _ t⁻¹ p.1]
      · simp only [Prod.smul_fst]
        rw [smul_comm, ← ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]
  choose P hPrel hPn using hplace
  by_cases hA : ∃ l0, E • (P l0).1 = 0 ∧ P l0 ≠ 0
  ·
    obtain ⟨l0, hEv, hP0⟩ := hA
    obtain ⟨φ, hφ⟩ := colHom_exists (V := V) e₁ δ D Kc k0 δx hδ 0
      (fun l => if l = l0 then δx • (P l).1 else 0)
      (fun l a => if l = l0 then (P l).2.1 a • s1 else 0)
      (fun l => if l = l0 then (P l).2.2 • η else 0)
      (by
        intro l; split_ifs with hl
        · subst hl; rw [smul_comm E δx, hEv, smul_zero]
        · exact smul_zero E)
      (by
        intro l a; split_ifs with hl
        · subst hl; rw [smul_comm e₁ ((P l).2.1 a) s1, he₁s1]
        · exact smul_zero e₁)
      (by
        intro l; split_ifs with hl
        · subst hl; rw [smul_comm E (P l).2.2 η, hEη, smul_comm (P l).2.2 δx η]
        · rw [smul_zero, smul_zero])
      (by
        intro l g hg
        split_ifs with hl
        · subst hl
          have hsum : ∀ a, Kc l a g • ((P l).2.1 a • s1) = (P l).2.1 a • (Kc l a g • s1) :=
            fun a => smul_comm _ _ _
          rw [LinearMap.zero_apply, zero_add]
          simp only [hsum]
          rw [smul_comm (k0 l g) (P l).2.2 η, hPrel l g hg, smul_sub,
            smul_comm ((((χ g)⁻¹ : T'ˣ) : T') • r g) δx (P l).1]
        · simp)
    refine ⟨φ, fun h0 => ?_⟩
    have key : ∀ x, colFreeMap (0 : Ymod r χ E →ₗ[A] V) (fun l => if l = l0 then δx • (P l).1 else 0)
        (fun l a => if l = l0 then (P l).2.1 a • s1 else 0)
        (fun l => if l = l0 then (P l).2.2 • η else 0) x = 0 := by
      intro x; rw [← hφ, h0, LinearMap.zero_apply]
    have hne : (P l0).1 ≠ 0 ∨ (∃ a, (P l0).2.1 a ≠ 0) ∨ (P l0).2.2 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hP0 (Prod.ext hc.1 (Prod.ext (funext hc.2.1) hc.2.2))
    rcases hne with hv | ⟨a, ha⟩ | hc0
    · have := key (colGenJ 0 l0 1 0 0)
      simp only [colFreeMap_colGen] at this
      simp [hv, hδx] at this
    · have := key (colGenJ 0 l0 0 (Pi.single a 1) 0)
      simp only [colFreeMap_colGen] at this
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
        (fun h => absurd (Finset.mem_univ a) h)] at this
      simp [ha, hs10] at this
    · have := key (colGenJ 0 l0 0 0 1)
      simp only [colFreeMap_colGen] at this
      simp [hc0, hη0] at this
  ·
    push Not at hA
    have hEP : ∀ l, E • (P l).1 = η := by
      intro l
      rcases hPn l with ⟨h1, h2⟩ | h
      · exact absurd (hA l h1) h2
      · exact h
    let φY : Ymod r χ E →ₗ[A] V := (LinearMap.toSpanSingleton A V w0).comp (Ymod r χ E).subtype
    have hφY : ∀ g, φY ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ =
        ((((χ g)⁻¹ : T'ˣ) : T') • r g) • η - η := by
      intro g
      simp only [φY, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.toSpanSingleton_apply,
        ycoc, mul_smul, hw0, sub_smul, one_smul]
    obtain ⟨φ, hφ⟩ := colHom_exists (V := V) e₁ δ D Kc k0 δx hδ φY
      (fun l => δx • (P l).1 - η)
      (fun l a => (P l).2.1 a • s1)
      (fun l => (P l).2.2 • η)
      (by intro l; rw [smul_sub, smul_comm E δx, hEP, hEη, sub_self])
      (by intro l a; rw [smul_comm e₁ ((P l).2.1 a) s1, he₁s1])
      (by intro l; rw [smul_comm E (P l).2.2 η, hEη, smul_comm (P l).2.2 δx η])
      (by
        intro l g hg
        have hsum : ∀ a, Kc l a g • ((P l).2.1 a • s1) = (P l).2.1 a • (Kc l a g • s1) :=
          fun a => smul_comm _ _ _
        rw [hφY]
        simp only [hsum]
        rw [smul_comm (k0 l g) (P l).2.2 η, hPrel l g hg, smul_sub, smul_sub,
          smul_comm ((((χ g)⁻¹ : T'ˣ) : T') • r g) δx (P l).1]
        abel)
    obtain ⟨g, hg⟩ := hfix η ⟨w0, by rw [DistribSMul.toLinearMap_apply, hw0]⟩ hη0
    refine ⟨φ, fun h0 => ?_⟩
    have := hφ (⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩, 0)
    rw [h0, LinearMap.zero_apply] at this
    simp only [colFreeMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, Prod.fst_zero,
      Prod.snd_zero, zero_smul, Finset.sum_const_zero, add_zero, hφY] at this
    exact hg (sub_eq_zero.mp this.symm)
end Formalism.NG
