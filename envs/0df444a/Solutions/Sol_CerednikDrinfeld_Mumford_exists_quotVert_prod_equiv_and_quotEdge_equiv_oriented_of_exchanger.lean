-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/22f54752-a192-5849-bdd6-a10254d3789f

import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem solution
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hc : 𝒯.Connected) (hb : 𝒯.Colorable 2) (w₀ : W)
    (Δ : Subgroup G) (γ₀ : G) (hγ₀ : γ₀ ∈ Δ) (hγ₀' : γ₀ ∉ typePreserving G 𝒯 w₀) :
    ∃ (εV : QuotVert (↥Δ) W × Fin 2 ≃ QuotVert (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W)
      (εE : QuotEdge (↥Δ) 𝒯 ≃
        {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}),

      (∀ w : W, vertexType 𝒯 w₀ w = 0 →
        εV (Quotient.mk (MulAction.orbitRel (↥Δ) W) w, 0) =
          Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) w) ∧
      (∀ w : W, vertexType 𝒯 w₀ w = 1 →
        εV (Quotient.mk (MulAction.orbitRel (↥Δ) W) w, 1) =
          Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) w) ∧

      (∀ d : 𝒯.Dart, vertexType 𝒯 w₀ d.fst = 0 →
        ((εE (Quotient.mk (MulAction.orbitRel (↥Δ) 𝒯.Dart) d) :
            {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}) :
            QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯) =
          Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯.Dart) d) ∧

      (∀ e : QuotEdge (↥Δ) 𝒯,
        (quotientDegeneracyData (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯).a ((εE e : {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}) : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯) =
          εV ((quotientDegeneracyData (↥Δ) 𝒯).a e, 0) ∧
        (quotientDegeneracyData (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯).b ((εE e : {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}) : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯) =
          εV ((quotientDegeneracyData (↥Δ) 𝒯).b e, 1)) ∧

      (∀ d : 𝒯.Dart,
        Nat.card (MulAction.stabilizer (↥Δ) d) = Nat.card (MulAction.stabilizer (↥(Δ ⊓ typePreserving G 𝒯 w₀)) d)) := by
  classical
  obtain ⟨hadj, hmul, -⟩ := CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter G 𝒯 hc hb w₀

  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hne : ∀ x : ZMod 2, x + 1 ≠ x := by decide
  have hkey : ∀ x i : ZMod 2, x ≠ i → x + 1 = i := by decide
  have hkey2 : ∀ x : ZMod 2, x + 1 = (1 : Fin 2) ↔ x = (0 : Fin 2) := by decide
  have hz0 : ∀ x : ZMod 2, x = 0 ↔ x = (0 : Fin 2) := by decide
  have hz1 : ∀ x : ZMod 2, x = 1 ↔ x = (1 : Fin 2) := by decide

  have hflip : ∀ g : G, g ∉ typePreserving G 𝒯 w₀ → ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w + 1 := by
    intro g hg w
    rw [hmul g w]
    rcases h01 (vertexType 𝒯 w₀ (g • w₀)) with h | h
    · exact absurd ((mem_typePreserving_iff 𝒯 w₀ g).2 fun w' => by rw [hmul g w', h, zero_add]) hg
    · rw [h, add_comm]
  have hfix1 : ∀ (g : G) (w : W), vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w → g ∈ typePreserving G 𝒯 w₀ := by
    intro g w h
    by_contra hg
    have h' := hflip g hg w
    rw [h] at h'
    exact hne _ h'.symm
  have hpres : ∀ (g : G), g ∈ typePreserving G 𝒯 w₀ → ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w :=
    fun g hg w => (mem_typePreserving_iff 𝒯 w₀ g).1 hg w

  have hsmulΔ : ∀ (δ : ↥Δ) (w : W), δ • w = (δ : G) • w := fun _ _ => rfl
  have hsmulΔD : ∀ (δ : ↥Δ) (d : 𝒯.Dart), δ • d = (δ : G) • d := fun _ _ => rfl
  have hsmulP : ∀ (δ : ↥(Δ ⊓ typePreserving G 𝒯 w₀)) (w : W), δ • w = (δ : G) • w := fun _ _ => rfl
  have hsmulPD : ∀ (δ : ↥(Δ ⊓ typePreserving G 𝒯 w₀)) (d : 𝒯.Dart), δ • d = (δ : G) • d := fun _ _ => rfl

  let nf : Fin 2 → W → W := fun i w => if vertexType 𝒯 w₀ w = i then w else γ₀ • w
  let nfD : 𝒯.Dart → 𝒯.Dart := fun d => if vertexType 𝒯 w₀ d.fst = (0 : Fin 2) then d else γ₀ • d
  have hnf_type : ∀ (i : Fin 2) (w : W), vertexType 𝒯 w₀ (nf i w) = i := by
    intro i w
    by_cases h : vertexType 𝒯 w₀ w = i
    · simp only [nf, if_pos h]; exact h
    · simp only [nf, if_neg h]; rw [hflip γ₀ hγ₀' w]; exact hkey _ _ h
  have hnfD_type : ∀ d : 𝒯.Dart, vertexType 𝒯 w₀ (nfD d).fst = 0 := by
    intro d
    by_cases h : vertexType 𝒯 w₀ d.fst = (0 : Fin 2)
    · simp only [nfD, if_pos h]; exact (hz0 _).2 h
    · simp only [nfD, if_neg h]; rw [smul_dart_fst, hflip γ₀ hγ₀' d.fst]; exact (hz0 _).2 (hkey _ _ h)

  have hnf_mem : ∀ (i : Fin 2) (w : W), ∃ g : G, g ∈ Δ ∧ nf i w = g • w := by
    intro i w
    by_cases h : vertexType 𝒯 w₀ w = i
    · exact ⟨1, Δ.one_mem, by simp only [nf, if_pos h, one_smul]⟩
    · exact ⟨γ₀, hγ₀, by simp only [nf, if_neg h]⟩
  have hnfD_mem : ∀ d : 𝒯.Dart, ∃ g : G, g ∈ Δ ∧ nfD d = g • d := by
    intro d
    by_cases h : vertexType 𝒯 w₀ d.fst = (0 : Fin 2)
    · exact ⟨1, Δ.one_mem, by simp only [nfD, if_pos h, one_smul]⟩
    · exact ⟨γ₀, hγ₀, by simp only [nfD, if_neg h]⟩

  have hsame : ∀ (a b : W), vertexType 𝒯 w₀ a = vertexType 𝒯 w₀ b → (∃ g : G, g ∈ Δ ∧ a = g • b) →
      (Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) a : QuotVert (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) =
        Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) b := by
    rintro a b hab ⟨g, hg, rfl⟩
    have hgT : g ∈ typePreserving G 𝒯 w₀ := hfix1 g b hab
    exact Quotient.sound ⟨⟨g, Subgroup.mem_inf.2 ⟨hg, hgT⟩⟩, rfl⟩
  have hsameD : ∀ (a b : 𝒯.Dart), vertexType 𝒯 w₀ a.fst = vertexType 𝒯 w₀ b.fst → (∃ g : G, g ∈ Δ ∧ a = g • b) →
      (Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯.Dart) a : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯) =
        Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯.Dart) b := by
    rintro a b hab ⟨g, hg, rfl⟩
    have hgT : g ∈ typePreserving G 𝒯 w₀ := hfix1 g b.fst (by rw [← smul_dart_fst]; exact hab)
    exact Quotient.sound ⟨⟨g, Subgroup.mem_inf.2 ⟨hg, hgT⟩⟩, rfl⟩

  have hrel : ∀ a b : W, (MulAction.orbitRel (↥Δ) W).r a b ↔ ∃ g : G, g ∈ Δ ∧ a = g • b := by
    intro a b
    constructor
    · rintro ⟨δ, rfl⟩; exact ⟨δ, δ.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩; exact ⟨⟨g, hg⟩, rfl⟩
  have hrelD : ∀ a b : 𝒯.Dart, (MulAction.orbitRel (↥Δ) 𝒯.Dart).r a b ↔ ∃ g : G, g ∈ Δ ∧ a = g • b := by
    intro a b
    constructor
    · rintro ⟨δ, rfl⟩; exact ⟨δ, δ.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩; exact ⟨⟨g, hg⟩, rfl⟩

  let fV : QuotVert (↥Δ) W × Fin 2 → QuotVert (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W := fun p =>
    Quotient.liftOn p.1 (fun w => Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) (nf p.2 w))
      (by
        intro a b hab
        apply hsame
        · rw [hnf_type, hnf_type]
        · obtain ⟨g, hg, rfl⟩ := (hrel a b).1 hab
          obtain ⟨ga, hga, hga'⟩ := hnf_mem p.2 (g • b)
          obtain ⟨gb, hgb, hgb'⟩ := hnf_mem p.2 b
          refine ⟨ga * g * gb⁻¹, Δ.mul_mem (Δ.mul_mem hga hg) (Δ.inv_mem hgb), ?_⟩
          rw [hga', hgb', mul_smul, mul_smul, inv_smul_smul])
  let gV : QuotVert (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W → QuotVert (↥Δ) W × Fin 2 := fun x =>
    Quotient.liftOn x (fun w => (Quotient.mk (MulAction.orbitRel (↥Δ) W) w, (vertexType 𝒯 w₀ w : Fin 2)))
      (by
        rintro a b ⟨δ, rfl⟩
        refine Prod.ext ?_ ?_
        · exact Quotient.sound ⟨⟨(δ : G), (Subgroup.mem_inf.1 δ.2).1⟩, rfl⟩
        · show vertexType 𝒯 w₀ ((δ : G) • b) = vertexType 𝒯 w₀ b
          exact hpres _ (Subgroup.mem_inf.1 δ.2).2 b)
  have hfg : ∀ x, fV (gV x) = x := by
    intro x
    induction x using Quotient.inductionOn with
    | h w =>
      show Quotient.mk _ (nf (vertexType 𝒯 w₀ w) w) = Quotient.mk _ w
      simp only [nf, if_pos rfl]
  have hgf : ∀ p, gV (fV p) = p := by
    rintro ⟨x, i⟩
    induction x using Quotient.inductionOn with
    | h w =>
      show (Quotient.mk (MulAction.orbitRel (↥Δ) W) (nf i w), (vertexType 𝒯 w₀ (nf i w) : Fin 2)) = (Quotient.mk _ w, i)
      refine Prod.ext ?_ (hnf_type i w)
      obtain ⟨g, hg, hg'⟩ := hnf_mem i w
      exact Quotient.sound ((hrel _ _).2 ⟨g, hg, hg'⟩)
  let εV : QuotVert (↥Δ) W × Fin 2 ≃ QuotVert (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W := ⟨fV, gV, hgf, hfg⟩

  have hout : ∀ d : 𝒯.Dart, vertexType 𝒯 w₀
      ((Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯.Dart) d : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯).out.fst) =
        vertexType 𝒯 w₀ d.fst := by
    intro d
    obtain ⟨δ, hδ⟩ := Quotient.mk_out (s := MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯.Dart) d
    rw [← hδ]
    show vertexType 𝒯 w₀ ((δ : G) • d).fst = vertexType 𝒯 w₀ d.fst
    rw [smul_dart_fst]
    exact hpres _ (Subgroup.mem_inf.1 δ.2).2 d.fst
  let fE : QuotEdge (↥Δ) 𝒯 → {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} := fun e =>
    Quotient.liftOn e
      (fun d => ⟨Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯.Dart) (nfD d), by rw [hout]; exact hnfD_type d⟩)
      (by
        intro a b hab
        apply Subtype.ext
        apply hsameD
        · rw [hnfD_type, hnfD_type]
        · obtain ⟨g, hg, rfl⟩ := (hrelD a b).1 hab
          obtain ⟨ga, hga, hga'⟩ := hnfD_mem (g • b)
          obtain ⟨gb, hgb, hgb'⟩ := hnfD_mem b
          refine ⟨ga * g * gb⁻¹, Δ.mul_mem (Δ.mul_mem hga hg) (Δ.inv_mem hgb), ?_⟩
          rw [hga', hgb', mul_smul, mul_smul, inv_smul_smul])
  let gE : {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} → QuotEdge (↥Δ) 𝒯 := fun e =>
    Quotient.liftOn e.1 (fun d => Quotient.mk (MulAction.orbitRel (↥Δ) 𝒯.Dart) d)
      (by
        rintro a b ⟨δ, rfl⟩
        exact Quotient.sound ⟨⟨(δ : G), (Subgroup.mem_inf.1 δ.2).1⟩, rfl⟩)
  have hfgE : ∀ e, fE (gE e) = e := by
    rintro ⟨e, he⟩
    induction e using Quotient.inductionOn with
    | h d =>
      apply Subtype.ext
      show Quotient.mk _ (nfD d) = Quotient.mk _ d
      have h0 : vertexType 𝒯 w₀ d.fst = (0 : Fin 2) := (hz0 _).1 (by rw [← hout]; exact he)
      simp only [nfD, if_pos h0]
  have hgfE : ∀ e, gE (fE e) = e := by
    intro e
    induction e using Quotient.inductionOn with
    | h d =>
      show Quotient.mk (MulAction.orbitRel (↥Δ) 𝒯.Dart) (nfD d) = Quotient.mk _ d
      obtain ⟨g, hg, hg'⟩ := hnfD_mem d
      exact Quotient.sound ((hrelD _ _).2 ⟨g, hg, hg'⟩)
  let εE : QuotEdge (↥Δ) 𝒯 ≃ {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} := ⟨fE, gE, hgfE, hfgE⟩
  refine ⟨εV, εE, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro w hw
    have hw' : vertexType 𝒯 w₀ w = (0 : Fin 2) := (hz0 _).1 hw
    show Quotient.mk _ (nf 0 w) = Quotient.mk _ w
    simp only [nf, if_pos hw']
  ·
    intro w hw
    have hw' : vertexType 𝒯 w₀ w = (1 : Fin 2) := (hz1 _).1 hw
    show Quotient.mk _ (nf 1 w) = Quotient.mk _ w
    simp only [nf, if_pos hw']
  ·
    intro d hd
    have hd' : vertexType 𝒯 w₀ d.fst = (0 : Fin 2) := (hz0 _).1 hd
    show Quotient.mk _ (nfD d) = Quotient.mk _ d
    simp only [nfD, if_pos hd']
  ·
    intro e
    induction e using Quotient.inductionOn with
    | h d =>
      constructor
      · show Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) (nfD d).fst =
          Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) (nf 0 d.fst)
        by_cases h : vertexType 𝒯 w₀ d.fst = (0 : Fin 2)
        · simp only [nfD, nf, if_pos h]
        · simp only [nfD, nf, if_neg h, smul_dart_fst]
      · show Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) (nfD d).snd =
          Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) (nf 1 d.snd)
        have hs : vertexType 𝒯 w₀ d.snd = vertexType 𝒯 w₀ d.fst + 1 := hadj d.fst d.snd d.adj
        by_cases h : vertexType 𝒯 w₀ d.fst = (0 : Fin 2)
        · have h1 : vertexType 𝒯 w₀ d.snd = (1 : Fin 2) := by rw [hs]; exact (hkey2 _).2 h
          simp only [nfD, nf, if_pos h, if_pos h1]
        · have h1 : ¬ vertexType 𝒯 w₀ d.snd = (1 : Fin 2) := by rw [hs]; exact fun h' => h ((hkey2 _).1 h')
          simp only [nfD, nf, if_neg h, if_neg h1, smul_dart_snd]
  ·
    intro d
    refine Nat.card_congr ⟨fun δ => ⟨⟨(δ.1 : G), Subgroup.mem_inf.2 ⟨δ.1.2, hfix1 _ d.fst ?_⟩⟩, ?_⟩,
      fun δ => ⟨⟨(δ.1 : G), (Subgroup.mem_inf.1 δ.1.2).1⟩, ?_⟩, ?_, ?_⟩
    · have hδ : (δ.1 : G) • d = d := δ.2
      rw [← smul_dart_fst 𝒯 (δ.1 : G) d, hδ]
    · exact δ.2
    · exact δ.2
    · intro δ; rfl
    · intro δ; rfl

#print axioms solution

end S_CerednikDrinfeld_Mumford_exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger (solution)
