-- Prove2me | solution 1 for CorrClustBBC.Cautious.theorem_13
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:31:57.46253+00:00
-- url     : https://prove2.me/submissions/b959e81b-324d-4bcf-9154-4dbeec24f986

import Definitions.Def_CorrClustBBC_Cautious_Setting
import Init
import Mathlib


section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangle_forces_mistake (G : SimpleGraph V) (D : Setoid V)
    {T : Finset V} (hT : IsErroneous G T) :
    ∃ u ∈ T, ∃ v ∈ T, IsMistake G D.r u v := by
  obtain ⟨a,b,c,rfl,hab,hac,hbc,habp,hacp,hbcn⟩ := hT
  by_cases hrab : D.r a b
  · by_cases hrac : D.r a c
    · exact ⟨b, by simp, c, by simp, hbc, Or.inr ⟨hbcn,D.trans (D.symm hrab) hrac⟩⟩
    · exact ⟨a, by simp, c, by simp, hac, Or.inl ⟨hacp,hrac⟩⟩
  · exact ⟨a, by simp, b, by simp, hab, Or.inl ⟨habp,hrab⟩⟩

noncomputable def mistakePairs (G : SimpleGraph V) (D : Setoid V) : Finset (Sym2 V) :=
  univ.filter (fun e => ∃ u v, e = s(u,v) ∧ IsMistake G D.r u v)

theorem pair_subset (u v : V) (T : Finset V) :
    (s(u,v) : Sym2 V).toFinset ⊆ T ↔ u ∈ T ∧ v ∈ T := by
  simp [Sym2.toFinset_mk_eq, Finset.insert_subset_iff]

theorem triangle_has_bad_pair (G : SimpleGraph V) (D : Setoid V)
    {T : Finset V} (hT : IsErroneous G T) :
    ∃ e ∈ mistakePairs G D, e.toFinset ⊆ T := by
  obtain ⟨u,hu,v,hv,hm⟩ := triangle_forces_mistake G D hT
  exact ⟨s(u,v), by simp only [mistakePairs,mem_filter,mem_univ,true_and]; exact ⟨u,v,rfl,hm⟩,
    (pair_subset u v T).mpr ⟨hu,hv⟩⟩

theorem packing_bound (G : SimpleGraph V) (w : Finset V → ℝ)
    (hw : IsFracPacking G w) (D : Setoid V) :
    ∑ T, w T ≤ (mistakes G D.r : ℝ) := by
  classical
  let M := mistakePairs G D
  have hc : ∀ T, w T ≤ ∑ e ∈ M, if e.toFinset ⊆ T then w T else 0 := by
    intro T
    by_cases hz : w T = 0
    · simp [hz]
    obtain ⟨e,he,het⟩ := triangle_has_bad_pair G D (hw.2.1 T hz)
    calc
      w T = (if e.toFinset ⊆ T then w T else 0) := by simp [het]
      _ ≤ ∑ e ∈ M, if e.toFinset ⊆ T then w T else 0 :=
        by
          apply single_le_sum (f := fun i : Sym2 V => if i.toFinset ⊆ T then w T else 0)
          · intro i _; split
            · exact hw.1 T
            · exact le_rfl
          · exact he
  calc
    ∑ T, w T ≤ ∑ T, ∑ e ∈ M, if e.toFinset ⊆ T then w T else 0 :=
      sum_le_sum (fun T _ => hc T)
    _ = ∑ e ∈ M, ∑ T : Finset V, if e.toFinset ⊆ T then w T else 0 := sum_comm
    _ ≤ ∑ e ∈ M, (1 : ℝ) := by
      apply sum_le_sum
      intro e he
      obtain ⟨u,v,rfl,hm⟩ := (mem_filter.mp (show e ∈ mistakePairs G D from he)).2
      simpa only [pair_subset, ← sum_filter] using hw.2.2 u v hm.1
    _ = (mistakes G D.r : ℝ) := by simp [M,mistakePairs,mistakes]

end Queelius.Correlation

end

section
namespace Queelius.Correlation
open Finset CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem overlap_lower (A B C : Finset V) :
    ((A ∩ C).card : ℝ) + ((B ∩ C).card : ℝ) ≤ (C.card : ℝ) + ((A ∩ B).card : ℝ) := by
  have h₁ : (A ∩ C ∪ B ∩ C).card ≤ C.card := card_le_card (by intro x hx; aesop)
  have h₂ : ((A ∩ C) ∩ (B ∩ C)).card ≤ (A ∩ B).card := card_le_card (by intro x hx; aesop)
  have h₃ := card_union_add_card_inter (A ∩ C) (B ∩ C)
  exact_mod_cast (show (A ∩ C).card + (B ∩ C).card ≤ C.card + (A ∩ B).card by omega)

theorem diff_upper (A B C : Finset V) :
    ((A \ B).card : ℝ) ≤ ((A \ C).card : ℝ) + ((C \ B).card : ℝ) := by
  have h : A \ B ⊆ (A \ C) ∪ (C \ B) := by
    intro x hx
    by_cases hc : x ∈ C <;> simp_all
  exact_mod_cast (card_le_card h).trans (card_union_le _ _)

theorem disjoint_overlap_upper (A B C D : Finset V) (hCD : Disjoint C D) :
    ((A ∩ B).card : ℝ) ≤ ((A \ C).card : ℝ) + ((B \ D).card : ℝ) := by
  have h : A ∩ B ⊆ (A \ C) ∪ (B \ D) := by
    intro x hx
    have hd := disjoint_left.mp hCD
    simp only [mem_inter,mem_union,mem_sdiff] at *
    by_cases hc : x ∈ C
    · exact Or.inr ⟨hx.2, fun h => hd hc h⟩
    · exact Or.inl ⟨hx.1,hc⟩
  exact_mod_cast (card_le_card h).trans (card_union_le _ _)

theorem card_split (A C : Finset V) :
    (A.card : ℝ) = ((A ∩ C).card : ℝ) + ((A \ C).card : ℝ) := by
  exact_mod_cast (card_inter_add_card_sdiff A C).symm

theorem inter_bound (A C : Finset V) : ((A ∩ C).card : ℝ) ≤ (C.card : ℝ) := by
  exact_mod_cast card_le_card inter_subset_right

theorem nbhd_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    {R : Finset V} {v : V} (hv : v ∈ R) : posNbhd G R v ⊆ R := by
  intro x hx
  simp only [posNbhd,mem_insert,mem_filter] at hx
  rcases hx with rfl | hx
  · exact hv
  · exact hx.1

theorem inter_diff (A C R : Finset V) (hAR : A ⊆ R) : A ∩ (R \ C) = A \ C := by
  ext x
  simp only [mem_inter,mem_sdiff]
  exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,hAR h.1,h.2⟩⟩

end Queelius.Correlation

end

section
namespace Queelius.Correlation.Controls
open Finset Classical CorrClustBBC.Cautious

def pathGraph : SimpleGraph (Fin 3) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0)
  symm := ⟨by intro u v h; exact ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance : DecidableRel pathGraph.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v ∧ (u=0 ∨ v=0)))

theorem full_triangle_erroneous : IsErroneous pathGraph (univ : Finset (Fin 3)) := by
  refine ⟨0,1,2,?_,by decide,by decide,by decide,by decide,by decide,by decide⟩
  ext i; fin_cases i <;> simp

noncomputable def unitTriangle (T : Finset (Fin 3)) : ℝ := if T = univ then 1 else 0

theorem unit_packing : IsFracPacking pathGraph unitTriangle := by
  refine ⟨fun T => by unfold unitTriangle; positivity,?_,?_⟩
  · intro T h
    by_cases he : T = univ
    · subst T; exact full_triangle_erroneous
    · simp [unitTriangle,he] at h
  · intro u v _
    simp [unitTriangle]

theorem unit_weight : ∑ T : Finset (Fin 3), unitTriangle T = 1 := by
  simp [unitTriangle]

theorem universal_mistakes : mistakes pathGraph (fun _ _ => True) = 1 := by
  classical
  have he : (univ.filter (fun e : Sym2 (Fin 3) => ∃ u v, e = s(u,v) ∧
      IsMistake pathGraph (fun _ _ => True) u v)) = {s(1,2)} := by
    ext e
    simp [IsMistake,pathGraph,Fin.exists_fin_succ]
    all_goals simp only [show (s(1,0) : Sym2 (Fin 3)) = s(0,1) from Sym2.eq_swap,
      show (s(2,0) : Sym2 (Fin 3)) = s(0,2) from Sym2.eq_swap,
      show (s(2,1) : Sym2 (Fin 3)) = s(1,2) from Sym2.eq_swap,or_self,or_assoc,or_self_left,imp_self]
  convert congrArg Finset.card he using 1 <;> norm_num [mistakes]

theorem discrete_mistakes : mistakes pathGraph (fun u v => u = v) = 2 := by
  classical
  have he : (univ.filter (fun e : Sym2 (Fin 3) => ∃ u v, e = s(u,v) ∧
      IsMistake pathGraph (fun u v => u=v) u v)) = {s(0,1),s(0,2)} := by
    ext e
    simp [IsMistake,pathGraph,Fin.exists_fin_succ]
    all_goals simp only [show (s(1,0) : Sym2 (Fin 3)) = s(0,1) from Sym2.eq_swap,
      show (s(2,0) : Sym2 (Fin 3)) = s(0,2) from Sym2.eq_swap,
      show (s(2,1) : Sym2 (Fin 3)) = s(1,2) from Sym2.eq_swap,or_self,or_assoc,or_self_left,imp_self]
  convert congrArg Finset.card he using 1
  · unfold mistakes
    congr 1
    ext e
    simp only [mem_filter,mem_univ,true_and]
  · symm
    rw [card_insert_of_notMem]
    · simp
    · simp [Sym2.eq_iff]

theorem no_double_count : (s(1,2) : Sym2 (Fin 3)) = s(2,1) := Sym2.eq_swap

theorem diagonal_not_mistake {V : Type*} (G : SimpleGraph V) (r : V → V → Prop) (v : V) :
    ¬ IsMistake G r v v := by simp [IsMistake]

def fakeTogether (u v : Fin 3) : Prop := u = v ∨ pathGraph.Adj u v

instance : DecidableRel fakeTogether := fun u v => inferInstanceAs (Decidable (u=v ∨ pathGraph.Adj u v))

theorem fake_reflexive (u : Fin 3) : fakeTogether u u := Or.inl rfl

theorem fake_symmetric : Symmetric fakeTogether := by
  intro u v h
  exact h.elim (fun he => Or.inl he.symm) (fun he => Or.inr ⟨he.1.symm,he.2.symm⟩)

theorem transitivity_required : mistakes pathGraph fakeTogether = 0 := by
  simp [mistakes,IsMistake,fakeTogether]
  aesop

theorem fake_not_transitive : ¬ Transitive fakeTogether := by
  intro h
  have bad := h (show fakeTogether 1 0 by decide) (show fakeTogether 0 2 by decide)
  exact (show ¬ fakeTogether 1 2 by decide) bad

end Queelius.Correlation.Controls

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleMass (t : V→V→V→ℝ) (T : Finset V) : ℝ :=
  ∑ a,∑ b,∑ c,if T={a,b,c} then t a b c else 0

theorem sum_triple_swap (S : Finset (Finset V)) (f : Finset V→V→V→V→ℝ) :
    (∑T∈S,∑a,∑b,∑c,f T a b c)=∑a,∑b,∑c,∑T∈S,f T a b c := by
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  rw [sum_comm]

theorem triangle_mass_total (t : V→V→V→ℝ) :
    ∑ T,triangleMass t T=∑a,∑b,∑c,t a b c := by
  unfold triangleMass
  rw [sum_triple_swap]
  simp

theorem triangle_mass_nonneg (t : V→V→V→ℝ) (ht : ∀ a b c,0 ≤ t a b c) (T : Finset V) :
    0 ≤ triangleMass t T := by
  unfold triangleMass
  apply sum_nonneg
  intro a _
  apply sum_nonneg
  intro b _
  apply sum_nonneg
  intro c _
  split
  · exact ht a b c
  · exact le_rfl

theorem triangle_mass_support (G : SimpleGraph V) (t : V→V→V→ℝ)
    (ht : ∀ a b c,t a b c≠0 → IsErroneous G {a,b,c}) :
    ∀ T,triangleMass t T≠0 → IsErroneous G T := by
  intro T hT
  by_contra h
  apply hT
  unfold triangleMass
  apply sum_eq_zero
  intro a _
  apply sum_eq_zero
  intro b _
  apply sum_eq_zero
  intro c _
  by_cases he:T={a,b,c}
  · rw [if_pos he]
    by_contra hz
    exact h (he.symm ▸ ht a b c hz)
  · rw [if_neg he]

theorem triangle_mass_load (t : V→V→V→ℝ) (u v : V) :
    (∑T∈univ.filter (fun T : Finset V=>u∈T ∧ v∈T),triangleMass t T)=
    ∑a,∑b,∑c,if u∈({a,b,c}:Finset V) ∧ v∈({a,b,c}:Finset V) then t a b c else 0 := by
  unfold triangleMass
  rw [sum_triple_swap]
  simp

theorem triple_edge_charge (t : ℝ) (ht : 0 ≤ t) (u v a b c : V) (huv : u≠v) :
    (if u∈({a,b,c}:Finset V) ∧ v∈({a,b,c}:Finset V) then t else 0) ≤
      (if a=u ∧ b=v then t else 0)+(if b=u ∧ a=v then t else 0)+
      (if a=u ∧ c=v then t else 0)+(if c=u ∧ a=v then t else 0)+
      (if b=u ∧ c=v then t else 0)+(if c=u ∧ b=v then t else 0) := by
  by_cases h:u∈({a,b,c}:Finset V) ∧ v∈({a,b,c}:Finset V)
  · rw [if_pos h]
    simp only [mem_insert,mem_singleton] at h
    rcases h with ⟨hu,hv⟩
    rcases hu with hu|hu|hu <;> rcases hv with hv|hv|hv <;>
      subst_vars <;> simp_all <;> split_ifs <;> linarith
  · rw [if_neg h]
    positivity

theorem triangle_mass_load_le (t : V→V→V→ℝ) (ht : ∀ a b c,0 ≤ t a b c)
    (u v : V) (huv : u≠v) :
    (∑T∈univ.filter (fun T : Finset V=>u∈T ∧ v∈T),triangleMass t T) ≤
      (∑c,t u v c)+(∑c,t v u c)+(∑b,t u b v)+(∑b,t v b u)+
      (∑a,t a u v)+(∑a,t a v u) := by
  rw [triangle_mass_load]
  calc
    _ ≤ ∑a,∑b,∑c,((if a=u ∧ b=v then t a b c else 0)+(if b=u ∧ a=v then t a b c else 0)+
        (if a=u ∧ c=v then t a b c else 0)+(if c=u ∧ a=v then t a b c else 0)+
        (if b=u ∧ c=v then t a b c else 0)+(if c=u ∧ b=v then t a b c else 0)) := by
      apply sum_le_sum;intro a _
      apply sum_le_sum;intro b _
      apply sum_le_sum;intro c _
      exact triple_edge_charge _ (ht a b c) u v a b c huv
    _ = _ := by simp [sum_add_distrib,ite_and,sum_ite_irrel]

theorem packing_of_triple_weights (G : SimpleGraph V) (t : V→V→V→ℝ)
    (ht : ∀ a b c,0 ≤ t a b c)
    (herr : ∀ a b c,t a b c≠0 → IsErroneous G {a,b,c})
    (hload : ∀ u v,u≠v → (∑c,t u v c)+(∑c,t v u c)+(∑b,t u b v)+(∑b,t v b u)+
      (∑a,t a u v)+(∑a,t a v u) ≤ 1) : IsFracPacking G (triangleMass t) := by
  exact ⟨triangle_mass_nonneg t ht,triangle_mass_support G t herr,
    fun u v h=>(triangle_mass_load_le t ht u v h).trans (hload u v h)⟩
end Queelius.Correlation

end

section
namespace Queelius.Correlation
open Finset CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem clean_nbhd (G : SimpleGraph V) [DecidableRel G.Adj]
    (R C : Finset V) (hCR : C ⊆ R) (hC : IsClean G R δ44 C)
    (v w : V) (hv : v ∈ C) (hw : w ∈ C) :
    IsGood G R (3 * δ44) (posNbhd G R v) w := by
  let A := posNbhd G R v
  let B := posNbhd G R w
  have hAR : A ⊆ R := nbhd_subset G (hCR hv)
  have hBR : B ⊆ R := nbhd_subset G (hCR hw)
  obtain ⟨ha,hac⟩ := hC v hv
  obtain ⟨hb,hbc⟩ := hC w hw
  change (1-δ44)*(C.card:ℝ) ≤ ((A ∩ C).card:ℝ) at ha
  change (1-δ44)*(C.card:ℝ) ≤ ((B ∩ C).card:ℝ) at hb
  change ((A ∩ (R \ C)).card:ℝ) ≤ δ44*(C.card:ℝ) at hac
  change ((B ∩ (R \ C)).card:ℝ) ≤ δ44*(C.card:ℝ) at hbc
  rw [inter_diff A C R hAR] at hac
  rw [inter_diff B C R hBR] at hbc
  have hAs := card_split A C
  have hCs := card_split C A
  rw [inter_comm C A] at hCs
  have hAi := inter_bound A C
  have hAl := inter_bound C A
  rw [inter_comm C A] at hAl
  have hI := overlap_lower A B C
  have hD := diff_upper B A C
  have hc0 : (0:ℝ) ≤ C.card := Nat.cast_nonneg _
  change (1-3*δ44)*(A.card:ℝ) ≤ ((B ∩ A).card:ℝ) ∧
    ((B ∩ (R \ A)).card:ℝ) ≤ (3*δ44)*(A.card:ℝ)
  rw [inter_comm B A, inter_diff B A R hBR]
  norm_num [δ44] at *
  constructor <;> linarith

theorem clean_separation (G : SimpleGraph V) [DecidableRel G.Adj]
    (R X C C' : Finset V) (_hX : X ⊆ R) (hCR : C ⊆ R) (hC'R : C' ⊆ R)
    (hdisj : Disjoint C C') (hC : IsClean G R δ44 C) (hC' : IsClean G R δ44 C')
    (v₁ v₂ : V) (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C') :
    ¬ (IsGood G R (3 * δ44) X v₁ ∧ IsGood G R (3 * δ44) X v₂) := by
  intro h
  let A := posNbhd G R v₁
  let B := posNbhd G R v₂
  have hAR : A ⊆ R := nbhd_subset G (hCR hv₁)
  have hBR : B ⊆ R := nbhd_subset G (hC'R hv₂)
  obtain ⟨ha,hac⟩ := hC v₁ hv₁
  obtain ⟨hb,hbc⟩ := hC' v₂ hv₂
  obtain ⟨⟨hax,haxc⟩,⟨hbx,hbxc⟩⟩ := h
  change (1-δ44)*(C.card:ℝ) ≤ ((A ∩ C).card:ℝ) at ha
  change (1-δ44)*(C'.card:ℝ) ≤ ((B ∩ C').card:ℝ) at hb
  change ((A ∩ (R \ C)).card:ℝ) ≤ δ44*(C.card:ℝ) at hac
  change ((B ∩ (R \ C')).card:ℝ) ≤ δ44*(C'.card:ℝ) at hbc
  change (1-3*δ44)*(X.card:ℝ) ≤ ((A ∩ X).card:ℝ) at hax
  change (1-3*δ44)*(X.card:ℝ) ≤ ((B ∩ X).card:ℝ) at hbx
  change ((A ∩ (R \ X)).card:ℝ) ≤ (3*δ44)*(X.card:ℝ) at haxc
  change ((B ∩ (R \ X)).card:ℝ) ≤ (3*δ44)*(X.card:ℝ) at hbxc
  rw [inter_diff A C R hAR] at hac
  rw [inter_diff B C' R hBR] at hbc
  rw [inter_diff A X R hAR] at haxc
  rw [inter_diff B X R hBR] at hbxc
  have hAi := inter_bound C A
  rw [inter_comm C A] at hAi
  have hBi := inter_bound C' B
  rw [inter_comm C' B] at hBi
  have hAx := inter_bound A X
  have hBx := inter_bound B X
  have hAs := card_split A X
  have hBs := card_split B X
  have hLower := overlap_lower A B X
  have hUpper := disjoint_overlap_upper A B C C' hdisj
  have hcpos : (0:ℝ) < C.card := by exact_mod_cast card_pos.mpr ⟨v₁,hv₁⟩
  norm_num [δ44] at ha hb hac hbc hax hbx haxc hbxc
  linarith

end Queelius.Correlation

end

section
namespace Queelius.Correlation
open Finset CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem removes_subset {R A B : Finset V} (h : Removes G R A B) : B ⊆ A := by
  induction h with
  | done => exact Subset.rfl
  | drop hx hbad h ih => exact ih.trans (erase_subset _ _)

theorem removes_clean {R A B : Finset V} (h : Removes G R A B) :
    IsClean G R (3 * δ44) B := by
  induction h with
  | done h => exact h
  | drop hx hbad h ih => exact ih

theorem removes_exists (R A : Finset V) : ∃ B, Removes G R A B := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases h : ∀ x ∈ A, IsGood G R (3 * δ44) A x
    · exact ⟨A,Removes.done h⟩
    push Not at h
    obtain ⟨x,hx,hbad⟩ := h
    obtain ⟨B,hB⟩ := ih (A.erase x) (erase_ssubset hx)
    exact ⟨B,Removes.drop hx hbad hB⟩

theorem add_subset {R B : Finset V} (hBR : B ⊆ R) : addStep G R B ⊆ R := by
  intro x hx
  simp only [addStep,mem_union,mem_filter] at hx
  exact hx.elim (fun h => hBR h) (fun h => h.1)

theorem run_exists (R : Finset V) :
    ∃ L Z, Run G R L Z := by
  classical
  induction R using Finset.strongInductionOn with
  | _ R ih =>
    by_cases hR : R.Nonempty
    · by_cases hn : ∃ v ∈ R, ∃ B, Removes G R (posNbhd G R v) B ∧ (addStep G R B).Nonempty
      · obtain ⟨v,hv,B,hB,hne⟩ := hn
        have hsub : addStep G R B ⊆ R := add_subset G ((removes_subset G hB).trans (nbhd_subset G hv))
        have hproper : R \ addStep G R B ⊂ R := sdiff_ssubset hsub hne
        obtain ⟨L,Z,hRun⟩ := ih _ hproper
        exact ⟨(B,addStep G R B,R)::L,Z,Run.cluster hv hB rfl hne hRun⟩
      · refine ⟨[],R,Run.stop hR ?_⟩
        intro v hv
        obtain ⟨B,hB⟩ := removes_exists G R (posNbhd G R v)
        refine ⟨B,hB,?_⟩
        exact not_nonempty_iff_eq_empty.mp (fun he => hn ⟨v,hv,B,hB,he⟩)
    · have h : R = ∅ := not_nonempty_iff_eq_empty.mp hR
      subst R
      exact ⟨[],∅,Run.nil⟩

end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def badVertices (δ : ℝ) (C : Finset V) : Finset V :=
  C.filter (fun v=>¬IsGood G univ (δ/3) C v)

def cleanCore (δ : ℝ) (C : Finset V) : Finset V :=
  if ((badVertices G δ C).card:ℝ) ≤ (δ/3)*(C.card:ℝ) then C \ badVertices G δ C else ∅

theorem core_subset (δ : ℝ) (C : Finset V) : cleanCore G δ C ⊆ C := by
  unfold cleanCore
  split
  · exact sdiff_subset
  · exact empty_subset _

theorem core_clean (δ : ℝ) (hd0 : 0 ≤ δ) (hd1 : δ ≤ 1) (C : Finset V) :
    IsClean G univ δ (cleanCore G δ C) := by
  unfold cleanCore
  split
  next hB =>
    intro v hv
    have hvC := (mem_sdiff.mp hv).1
    have hg : IsGood G univ (δ/3) C v := by
      by_contra h
      exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨hvC,h⟩)
    let N := posNbhd G univ v
    let B := badVertices G δ C
    have hBC : B ⊆ C := filter_subset _ _
    have hsize : ((C \ B).card:ℝ)+(B.card:ℝ)=C.card := by
      exact_mod_cast card_sdiff_add_card_eq_card hBC
    have hinside : ((N∩C).card:ℝ) ≤ ((N∩(C\B)).card:ℝ)+(B.card:ℝ) := by
      have hs : N∩C ⊆ (N∩(C\B))∪B := by intro x hx;by_cases hb : x∈B <;> simp_all
      exact_mod_cast (card_le_card hs).trans (card_union_le _ _)
    have houtside : ((N∩(univ\(C\B))).card:ℝ) ≤ ((N∩(univ\C)).card:ℝ)+(B.card:ℝ) := by
      have hs : N∩(univ\(C\B)) ⊆ (N∩(univ\C))∪B := by intro x hx;by_cases hb : x∈B <;> simp_all
      exact_mod_cast (card_le_card hs).trans (card_union_le _ _)
    have hC0 : (0:ℝ) ≤ C.card := Nat.cast_nonneg _
    have hB0 : (0:ℝ) ≤ B.card := Nat.cast_nonneg _
    have hsizele : ((C\B).card:ℝ) ≤ C.card := by exact_mod_cast card_le_card sdiff_subset
    change (1-δ/3)*(C.card:ℝ) ≤ ((N∩C).card:ℝ) ∧
      ((N∩(univ\C)).card:ℝ) ≤ (δ/3)*(C.card:ℝ) at hg
    change (B.card:ℝ) ≤ (δ/3)*(C.card:ℝ) at hB
    change (1-δ)*((C\B).card:ℝ) ≤ ((N∩(C\B)).card:ℝ) ∧
      ((N∩(univ\(C\B))).card:ℝ) ≤ δ*((C\B).card:ℝ)
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hsizele),mul_nonneg hd0 hC0]
    · have hbδ : δ*(B.card:ℝ) ≤ (B.card:ℝ) := by nlinarith
      nlinarith
  next hB => simp [IsClean]

def keepVertex (δ : ℝ) (D : Setoid V) (v : V) : Prop := v∈cleanCore G δ (classOf D v)

def cleanupSetoid (δ : ℝ) (D : Setoid V) : Setoid V where
  r u v := u=v ∨ (D.r u v ∧ keepVertex G δ D u ∧ keepVertex G δ D v)
  iseqv := {
    refl := fun u=>Or.inl rfl
    symm := by
      intro u v h
      rcases h with h|⟨h,hu,hv⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨D.symm h,hv,hu⟩
    trans := by
      intro u v w h k
      rcases h with rfl|⟨h,hu,hv⟩
      · exact k
      rcases k with rfl|⟨k,hv,hw⟩
      · exact Or.inr ⟨h,hu,hv⟩
      · exact Or.inr ⟨D.trans h k,hu,hw⟩ }

theorem class_eq_of_related (D : Setoid V) {u v : V} (h : D.r u v) :
    classOf D u=classOf D v := by
  ext x
  simp only [classOf,mem_filter,mem_univ,true_and]
  exact ⟨fun hx=>D.trans (D.symm h) hx,fun hx=>D.trans h hx⟩

theorem cleanup_class_kept (δ : ℝ) (D : Setoid V) (v : V) (hv : keepVertex G δ D v) :
    classOf (cleanupSetoid G δ D) v=cleanCore G δ (classOf D v) := by
  ext u
  simp only [classOf,mem_filter,mem_univ,true_and]
  change (v=u ∨ (D.r v u ∧ keepVertex G δ D v ∧ keepVertex G δ D u)) ↔ u∈cleanCore G δ (classOf D v)
  constructor
  · rintro (rfl|⟨h,_,hu⟩)
    · exact hv
    · unfold keepVertex at hu
      rwa [class_eq_of_related D h]
  · intro hu
    have h : D.r v u := by
      have hh:=core_subset G δ (classOf D v) hu
      simpa only [classOf,mem_filter,mem_univ,true_and] using hh
    exact Or.inr ⟨h,hv,by unfold keepVertex;rw [←class_eq_of_related D h];exact hu⟩

theorem cleanup_class_removed (δ : ℝ) (D : Setoid V) (v : V) (hv : ¬keepVertex G δ D v) :
    classOf (cleanupSetoid G δ D) v={v} := by
  ext u
  simp only [classOf,mem_filter,mem_univ,true_and,cleanupSetoid,mem_singleton]
  change (v=u ∨ (D.r v u ∧ keepVertex G δ D v ∧ keepVertex G δ D u)) ↔ u=v
  simp only [hv,and_false,false_and,or_false]
  exact eq_comm

theorem cleanup_nonsingleton_clean (δ : ℝ) (hd0 : 0 ≤ δ) (hd1 : δ ≤ 1) (D : Setoid V) :
    NonsingletonClean G δ (cleanupSetoid G δ D) := by
  intro v hv
  by_cases hk : keepVertex G δ D v
  · rw [cleanup_class_kept G δ D v hk]
    exact core_clean G δ hd0 hd1 _
  · rw [cleanup_class_removed G δ D v hk,card_singleton] at hv
    omega

theorem cleanup_refines (δ : ℝ) (D : Setoid V) {u v : V}
    (h : (cleanupSetoid G δ D).r u v) : D.r u v := by
  rcases h with rfl|⟨h,_,_⟩
  · exact D.refl _
  · exact h
end Queelius.Correlation

end

section
namespace CorrClustBBC.Cautious
theorem lemma_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) (hw : IsFracPacking G w) (D : Setoid V) :
    ∑ T, w T ≤ (mistakes G D.r : ℝ) := Queelius.Correlation.packing_bound G w hw D
end CorrClustBBC.Cautious

namespace CorrClustBBC.Cautious
theorem lemma_8 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R C : Finset V) (hCR : C ⊆ R) (hC : IsClean G R δ44 C) (v w : V) (hv : v ∈ C) (hw : w ∈ C) :
    IsGood G R (3 * δ44) (posNbhd G R v) w := Queelius.Correlation.clean_nbhd G R C hCR hC v w hv hw
end CorrClustBBC.Cautious

namespace CorrClustBBC.Cautious
theorem lemma_9 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R X C C' : Finset V) (hX : X ⊆ R) (hCR : C ⊆ R) (hC'R : C' ⊆ R) (hdisj : Disjoint C C')
    (hC : IsClean G R δ44 C) (hC' : IsClean G R δ44 C') (v₁ v₂ : V) (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C') :
    ¬ (IsGood G R (3 * δ44) X v₁ ∧ IsGood G R (3 * δ44) X v₂) := Queelius.Correlation.clean_separation G R X C C' hX hCR hC'R hdisj hC hC' v₁ v₂ hv₁ hv₂
end CorrClustBBC.Cautious

end

section
namespace Queelius.Correlation
open Finset CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem removal_separation (G : SimpleGraph V) [DecidableRel G.Adj]
    (R A B C C' : Finset V) (hAR : A ⊆ R) (hCR : C ⊆ R) (hC'R : C' ⊆ R)
    (hdisj : Disjoint C C') (hC : IsClean G R δ44 C) (hC' : IsClean G R δ44 C')
    (hremove : Removes G R A B) (u v : V) (hu : u ∈ C) (hv : v ∈ C') :
    ¬ (u ∈ B ∧ v ∈ B) := by
  intro h
  exact clean_separation G R B C C' ((removes_subset G hremove).trans hAR)
    hCR hC'R hdisj hC hC' u v hu hv
    ⟨removes_clean G hremove u h.1, removes_clean G hremove v h.2⟩

end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

def relationPairs (Q : V → V → Prop) : Finset (Sym2 V) :=
  univ.filter (fun e=>∃u v,e=s(u,v) ∧ Q u v)
def relationNeighbors (Q : V → V → Prop) (v : V) : Finset V := univ.filter (Q v)

theorem neighbor_pair_image (Q : V → V → Prop) (hs : Symmetric Q) (v : V) :
    (relationNeighbors Q v).image (fun u=>s(v,u))=
      (relationPairs Q).filter (fun e=>v∈e.toFinset) := by
  ext e
  constructor
  · intro h
    obtain ⟨u,hu,rfl⟩:=mem_image.mp h
    simp only [relationNeighbors,mem_filter,mem_univ,true_and] at hu
    simp only [relationPairs,mem_filter,mem_univ,true_and]
    exact ⟨⟨v,u,rfl,hu⟩,by simp⟩
  · intro h
    obtain ⟨he,hv⟩:=mem_filter.mp h
    obtain ⟨a,b,rfl,hab⟩:=(mem_filter.mp he).2
    simp only [Sym2.toFinset_mk_eq,mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl
    · exact mem_image.mpr ⟨b,mem_filter.mpr ⟨mem_univ _,hab⟩,rfl⟩
    · exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,hs hab⟩,Sym2.eq_swap⟩

theorem pair_fixed_injective (v : V) : Function.Injective (fun u:V=>s(v,u)) := by
  intro a b h
  rcases Sym2.eq_iff.mp h with ⟨_,h⟩|⟨h,k⟩
  · exact h
  · exact k.trans h

theorem relation_degree_sum (Q : V → V → Prop) (hs : Symmetric Q)
    (hi : ∀v,¬Q v v) : ∑v,(relationNeighbors Q v).card=2*(relationPairs Q).card := by
  have hn (v : V) : (relationNeighbors Q v).card=
      ((relationPairs Q).filter (fun e=>v∈e.toFinset)).card := by
    rw [←neighbor_pair_image Q hs v,card_image_of_injective _ (pair_fixed_injective v)]
  simp_rw [hn,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  have he (e : Sym2 V) (he : e∈relationPairs Q) : (∑v,if v∈e.toFinset then (1:ℕ) else 0)=2 := by
    obtain ⟨u,v,rfl,h⟩:=(mem_filter.mp he).2
    have huv : u≠v:=by intro hh;subst v;exact hi u h
    have hf : univ.filter (fun x=>x∈(s(u,v):Sym2 V).toFinset)={u,v} := by
      ext x
      simp
    rw [←sum_filter,hf]
    simp [huv]
  simp_rw [sum_congr rfl he]
  simp [mul_comm]

theorem mistake_symmetric (G : SimpleGraph V) (D : Setoid V) : Symmetric (IsMistake G D.r) := by
  intro u v h
  refine ⟨Ne.symm h.1,?_⟩
  rcases h.2 with ⟨hg,hd⟩|⟨hg,hd⟩
  · exact Or.inl ⟨hg.symm,fun h=>hd (D.symm h)⟩
  · exact Or.inr ⟨fun h=>hg (h.symm),D.symm hd⟩

theorem mistake_degree_sum (G : SimpleGraph V) (D : Setoid V) :
    ∑v,(relationNeighbors (IsMistake G D.r) v).card=2*mistakes G D.r :=
  relation_degree_sum _ (mistake_symmetric G D) (fun _ h=>h.1 rfl)

variable (G : SimpleGraph V) [DecidableRel G.Adj]
theorem mistake_neighbors_partition (D : Setoid V) (v : V) :
    relationNeighbors (IsMistake G D.r) v=
      (classOf D v\posNbhd G univ v)∪(posNbhd G univ v\classOf D v) := by
  ext u
  by_cases h : v=u
  · subst u
    simp [relationNeighbors,IsMistake,classOf,posNbhd,D.refl]
  · have hu : u≠v:=Ne.symm h
    simp [relationNeighbors,IsMistake,classOf,posNbhd,h,hu]
    tauto

theorem bad_vertex_degree (δ : ℝ) (D : Setoid V) (v : V)
    (hv : v∈badVertices G δ (classOf D v)) :
    (δ/3)*((classOf D v).card:ℝ) < (relationNeighbors (IsMistake G D.r) v).card := by
  let C:=classOf D v
  let N:=posNbhd G univ v
  have hbad : ¬IsGood G univ (δ/3) C v := (mem_filter.mp hv).2
  have hdeg : ((relationNeighbors (IsMistake G D.r) v).card:ℝ)=
      ((C\N).card:ℝ)+((N\C).card:ℝ) := by
    rw [mistake_neighbors_partition G D v,card_union_of_disjoint disjoint_sdiff_sdiff]
    push_cast
    rfl
  have hsplit:=card_split C N
  rw [inter_comm C N] at hsplit
  have hnR : N⊆(univ:Finset V):=subset_univ _
  unfold IsGood at hbad
  change ¬((1-δ/3)*(C.card:ℝ) ≤ ((N∩C).card:ℝ) ∧
    ((N∩(univ\C)).card:ℝ) ≤ (δ/3)*(C.card:ℝ)) at hbad
  rw [inter_diff N C univ hnR] at hbad
  have h0 : (0:ℝ) ≤ (C\N).card:=Nat.cast_nonneg _
  have h1 : (0:ℝ) ≤ (N\C).card:=Nat.cast_nonneg _
  rcases not_and_or.mp hbad with h|h
  · have h:=lt_of_not_ge h
    linarith
  · have h:=lt_of_not_ge h
    linarith
end Queelius.Correlation

end

section
namespace Queelius.Correlation
open Finset CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem good_transfer (R B C : Finset V) (hCR : C ⊆ R) (hC : IsClean G R δ44 C)
    (u w : V) (hu : u∈C) (hw : w∈C) (hgood : IsGood G R (3*δ44) B u) :
    IsGood G R (7*δ44) B w := by
  let A:=posNbhd G R u
  let W:=posNbhd G R w
  have hAR : A⊆R:=nbhd_subset G (hCR hu)
  have hWR : W⊆R:=nbhd_subset G (hCR hw)
  obtain ⟨huc,huout⟩:=hC u hu
  obtain ⟨hwc,hwout⟩:=hC w hw
  obtain ⟨hub,hubout⟩:=hgood
  change (1-δ44)*(C.card:ℝ)≤((A∩C).card:ℝ) at huc
  change ((A∩(R\C)).card:ℝ)≤δ44*(C.card:ℝ) at huout
  change (1-δ44)*(C.card:ℝ)≤((W∩C).card:ℝ) at hwc
  change ((W∩(R\C)).card:ℝ)≤δ44*(C.card:ℝ) at hwout
  change (1-3*δ44)*(B.card:ℝ)≤((A∩B).card:ℝ) at hub
  change ((A∩(R\B)).card:ℝ)≤(3*δ44)*(B.card:ℝ) at hubout
  rw [inter_diff A C R hAR] at huout
  rw [inter_diff W C R hWR] at hwout
  rw [inter_diff A B R hAR] at hubout
  have hCA:=card_split C A
  have hCW:=card_split C W
  have hBA:=card_split B A
  have hWB:=card_split B W
  rw [inter_comm C A] at hCA
  rw [inter_comm C W] at hCW
  rw [inter_comm B A] at hBA
  rw [inter_comm B W] at hWB
  have ha:=card_split A B
  have hac:=inter_bound C A
  rw [inter_comm C A] at hac
  have hab:=inter_bound A B
  have hBC:=diff_upper B C A
  have hCB:=diff_upper C B A
  have hBW:=diff_upper B W C
  have hWBC:=diff_upper W B C
  have hb0 : (0:ℝ)≤B.card:=Nat.cast_nonneg _
  change (1-7*δ44)*(B.card:ℝ)≤((W∩B).card:ℝ) ∧
    ((W∩(R\B)).card:ℝ)≤(7*δ44)*(B.card:ℝ)
  rw [inter_diff W B R hWR]
  norm_num [δ44] at huc huout hwc hwout hub hubout ⊢
  constructor <;> linarith

theorem disjoint_rejects_good (R B C : Finset V) (hCR : C⊆R) (hC : IsClean G R δ44 C)
    (hBC : Disjoint B C) (u : V) (hu : u∈C) : ¬IsGood G R (7*δ44) B u := by
  intro h
  let A:=posNbhd G R u
  have hAR : A⊆R:=nbhd_subset G (hCR hu)
  obtain ⟨huc,huout⟩:=hC u hu
  obtain ⟨hub,hubout⟩:=h
  change (1-δ44)*(C.card:ℝ)≤((A∩C).card:ℝ) at huc
  change ((A∩(R\C)).card:ℝ)≤δ44*(C.card:ℝ) at huout
  change (1-7*δ44)*(B.card:ℝ)≤((A∩B).card:ℝ) at hub
  change ((A∩(R\B)).card:ℝ)≤(7*δ44)*(B.card:ℝ) at hubout
  rw [inter_diff A C R hAR] at huout
  rw [inter_diff A B R hAR] at hubout
  have h₁ : (A∩B).card≤(A\C).card:=card_le_card (by
    intro x hx
    exact mem_sdiff.mpr ⟨(mem_inter.mp hx).1,fun hc=>disjoint_left.mp hBC (mem_inter.mp hx).2 hc⟩)
  have h₂ : (A∩C).card≤(A\B).card:=card_le_card (by
    intro x hx
    exact mem_sdiff.mpr ⟨(mem_inter.mp hx).1,fun hb=>disjoint_left.mp hBC hb (mem_inter.mp hx).2⟩)
  have h₁r : ((A∩B).card:ℝ)≤(A\C).card:=by exact_mod_cast h₁
  have h₂r : ((A∩C).card:ℝ)≤(A\B).card:=by exact_mod_cast h₂
  have hcpos : (0:ℝ)<C.card:=by exact_mod_cast card_pos.mpr ⟨u,hu⟩
  norm_num [δ44] at huc huout hub hubout
  linarith

theorem add_preserves_cluster (R B C : Finset V) (hCR : C⊆R) (hC : IsClean G R δ44 C)
    (hB : IsClean G R (3*δ44) B) : C⊆addStep G R B ∨ Disjoint C (addStep G R B) := by
  classical
  by_cases hBC : Disjoint B C
  · right
    apply disjoint_left.mpr
    intro u hu ha
    simp only [addStep,mem_union,mem_filter] at ha
    rcases ha with hb|⟨_,hg⟩
    · exact disjoint_left.mp hBC hb hu
    · exact disjoint_rejects_good G R B C hCR hC hBC u hu hg
  · left
    obtain ⟨u,huB,huC⟩:=not_disjoint_iff.mp hBC
    intro w hw
    exact mem_union_right _ (mem_filter.mpr ⟨hCR hw,good_transfer G R B C hCR hC u w huC hw (hB u huB)⟩)

theorem nbhd_mono (R S : Finset V) (hRS : R⊆S) (v : V) : posNbhd G R v⊆posNbhd G S v := by
  intro x hx
  simp only [posNbhd,mem_insert,mem_filter] at hx ⊢
  exact hx.elim Or.inl (fun h=>Or.inr ⟨hRS h.1,h.2⟩)

theorem clean_restrict (R S C : Finset V) (hRS : R⊆S) (hCR : C⊆R)
    (d : ℝ) (hC : IsClean G S d C) : IsClean G R d C := by
  intro v hv
  have he : posNbhd G R v∩C=posNbhd G S v∩C := by
    ext x
    simp only [mem_inter,posNbhd,mem_insert,mem_filter]
    constructor
    · rintro ⟨h,hc⟩
      exact ⟨h.elim Or.inl (fun h=>Or.inr ⟨hRS h.1,h.2⟩),hc⟩
    · rintro ⟨h,hc⟩
      exact ⟨h.elim Or.inl (fun h=>Or.inr ⟨hCR hc,h.2⟩),hc⟩
  have hsub : posNbhd G R v∩(R\C)⊆posNbhd G S v∩(S\C) := by
    intro x hx
    exact mem_inter.mpr ⟨nbhd_mono G R S hRS v (mem_inter.mp hx).1,
      mem_sdiff.mpr ⟨hRS (mem_sdiff.mp (mem_inter.mp hx).2).1,(mem_sdiff.mp (mem_inter.mp hx).2).2⟩⟩
  constructor
  · rw [he]
    exact (hC v hv).1
  · have hc : ((posNbhd G R v∩(R\C)).card:ℝ)≤(posNbhd G S v∩(S\C)).card := by exact_mod_cast card_le_card hsub
    exact hc.trans (hC v hv).2
end Queelius.Correlation

end

section
namespace Queelius.Correlation
open Finset CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_sets_subset {R Z : Finset V} {L : List (Finset V × Finset V × Finset V)}
    (hrun : Run G R L Z) : ∀ p∈L,p.1⊆p.2.1 ∧ p.2.1⊆p.2.2 ∧ p.2.2⊆R := by
  classical
  induction hrun with
  | nil => simp
  | stop => simp
  | @cluster R B A L Z v hv hremove hA hne hr ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · refine ⟨?_,?_,Subset.rfl⟩
      · simpa only [hA,addStep] using (subset_union_left : B⊆B∪R.filter (fun y=>IsGood G R (7*δ44) B y))
      · rw [hA]
        exact add_subset G ((removes_subset G hremove).trans (nbhd_subset G hv))
    · obtain ⟨hB,hA,hR⟩:=ih p hp
      exact ⟨hB,hA,hR.trans sdiff_subset⟩

theorem run_intact_cluster {R Z : Finset V} {L : List (Finset V × Finset V × Finset V)}
    (hrun : Run G R L Z) : ∀ C : Finset V,C⊆R→IsClean G R δ44 C→
      ∀ p∈L,C⊆p.2.2 ∨ Disjoint C p.2.2 := by
  induction hrun with
  | nil => simp
  | stop => simp
  | @cluster R B A L Z v hv hremove hA hne hr ih =>
    intro C hCR hC p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · exact Or.inl hCR
    · have hstep:=add_preserves_cluster G R B C hCR hC (removes_clean G hremove)
      rw [←hA] at hstep
      rcases hstep with hcap|hdisj
      · right
        apply disjoint_left.mpr
        intro u hu hpR
        have huRA:=(run_sets_subset G hr p hp).2.2 hpR
        exact (mem_sdiff.mp huRA).2 (hcap hu)
      · have hCR' : C⊆R\A := by
          intro u hu
          exact mem_sdiff.mpr ⟨hCR hu,fun ha=>disjoint_left.mp hdisj hu ha⟩
        exact ih C hCR' (clean_restrict G (R\A) R C sdiff_subset hCR' δ44 hC) p hp

theorem run_removal_clean {R Z : Finset V} {L : List (Finset V × Finset V × Finset V)}
    (hrun : Run G R L Z) : ∀ p∈L,IsClean G p.2.2 (3*δ44) p.1 := by
  induction hrun with
  | nil => simp
  | stop => simp
  | @cluster R B A L Z v hv hremove hA hne hr ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · exact removes_clean G hremove
    · exact ih p hp

theorem class_mem_self (D : Setoid V) (u : V) : u∈classOf D u := by
  simp only [classOf,mem_filter,mem_univ,true_and]
  exact D.refl u

theorem classes_disjoint (D : Setoid V) (u v : V) (h : ¬D.r u v) :
    Disjoint (classOf D u) (classOf D v) := by
  apply disjoint_left.mpr
  intro x hu hv
  simp only [classOf,mem_filter,mem_univ,true_and] at hu hv
  exact h (D.trans hu (D.symm hv))

theorem run_removal_separation (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G univ L Z) :
    ∀ p∈L,∀ u∈p.1,∀ v∈p.1,2≤(classOf D u).card→2≤(classOf D v).card→D.r u v := by
  intro p hp u hu v hv hu2 hv2
  by_contra h
  have hs:=run_sets_subset G hrun p hp
  have hBR : p.1⊆p.2.2:=hs.1.trans hs.2.1
  have hCu : classOf D u⊆p.2.2 := by
    rcases run_intact_cluster G hrun (classOf D u) (subset_univ _) (hD u hu2) p hp with hc|hd
    · exact hc
    · exact False.elim (disjoint_left.mp hd (class_mem_self D u) (hBR hu))
  have hCv : classOf D v⊆p.2.2 := by
    rcases run_intact_cluster G hrun (classOf D v) (subset_univ _) (hD v hv2) p hp with hc|hd
    · exact hc
    · exact False.elim (disjoint_left.mp hd (class_mem_self D v) (hBR hv))
  have huc:=clean_restrict G p.2.2 univ (classOf D u) (subset_univ _) hCu δ44 (hD u hu2)
  have hvc:=clean_restrict G p.2.2 univ (classOf D v) (subset_univ _) hCv δ44 (hD v hv2)
  exact clean_separation G p.2.2 p.1 (classOf D u) (classOf D v) hBR hCu hCv
    (classes_disjoint D u v h) huc hvc u v (class_mem_self D u) (class_mem_self D v)
    ⟨run_removal_clean G hrun p hp u hu,run_removal_clean G hrun p hp v hv⟩
end Queelius.Correlation

end

section
namespace Queelius.Correlation
open Finset CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem near_cluster_good (R A C : Finset V) (hCR : C⊆R) (hC : IsClean G R δ44 C)
    (hout : ((A\C).card:ℝ)≤δ44*(C.card:ℝ)) (hmiss : ((C\A).card:ℝ)≤δ44*(C.card:ℝ))
    (w : V) (hw : w∈C) : IsGood G R (3*δ44) A w := by
  let W:=posNbhd G R w
  have hWR : W⊆R:=nbhd_subset G (hCR hw)
  obtain ⟨hWC,hWout⟩:=hC w hw
  change (1-δ44)*(C.card:ℝ)≤((W∩C).card:ℝ) at hWC
  change ((W∩(R\C)).card:ℝ)≤δ44*(C.card:ℝ) at hWout
  rw [inter_diff W C R hWR] at hWout
  have hCA:=card_split C A
  have hCW:=card_split C W
  have hAW:=card_split A W
  have hCAle:=inter_bound C A
  rw [inter_comm C W] at hCW
  rw [inter_comm A W] at hAW
  have hAWle:=diff_upper A W C
  have hWAle:=diff_upper W A C
  change (1-3*δ44)*(A.card:ℝ)≤((W∩A).card:ℝ) ∧
    ((W∩(R\A)).card:ℝ)≤(3*δ44)*(A.card:ℝ)
  rw [inter_diff W A R hWR]
  norm_num [δ44] at hout hmiss hWC hWout ⊢
  constructor <;> linarith

theorem intermediate_near (R C : Finset V) (hCR : C⊆R) (hC : IsClean G R δ44 C)
    (v : V) (hv : v∈C) (A : Finset V) (hA : A⊆posNbhd G R v)
    (hkeep : posNbhd G R v∩C⊆A) :
    ((A\C).card:ℝ)≤δ44*(C.card:ℝ) ∧ ((C\A).card:ℝ)≤δ44*(C.card:ℝ) := by
  have hN:=hC v hv
  unfold IsGood at hN
  rw [inter_diff _ C R (nbhd_subset G (hCR hv))] at hN
  have hsub : A\C⊆posNbhd G R v\C := sdiff_subset_sdiff_left C hA
  have ho : ((A\C).card:ℝ)≤(posNbhd G R v\C).card := by exact_mod_cast card_le_card hsub
  have hm : C\A⊆C\posNbhd G R v := by
    intro u hu
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp hu).1,fun h=>
      (mem_sdiff.mp hu).2 (hkeep (mem_inter.mpr ⟨h,(mem_sdiff.mp hu).1⟩))⟩
  have hmc : ((C\A).card:ℝ)≤(C\posNbhd G R v).card := by exact_mod_cast card_le_card hm
  have hs:=card_split C (posNbhd G R v)
  rw [inter_comm C] at hs
  exact ⟨ho.trans hN.2,by linarith [hN.1]⟩

theorem removes_keep_pivot_cluster (R C : Finset V) (hCR : C⊆R) (hC : IsClean G R δ44 C)
    (v : V) (hv : v∈C) {A B : Finset V} (hr : Removes G R A B)
    (hA : A⊆posNbhd G R v) (hkeep : posNbhd G R v∩C⊆A) : posNbhd G R v∩C⊆B := by
  induction hr with
  | done => exact hkeep
  | @drop A B x hx hbad hr ih =>
    have hnear:=intermediate_near G R C hCR hC v hv A hA hkeep
    have hxc : x∉C := fun hc=>hbad (near_cluster_good G R A C hCR hC hnear.1 hnear.2 x hc)
    apply ih ((erase_subset _ _).trans hA)
    intro u hu
    apply mem_erase.mpr
    exact ⟨fun he=>hxc (he ▸ (mem_inter.mp hu).2),hkeep hu⟩

theorem pivot_captures_cluster (R C : Finset V) (hCR : C⊆R) (hC : IsClean G R δ44 C)
    (v : V) (hv : v∈C) (B : Finset V) (hr : Removes G R (posNbhd G R v) B) :
    C⊆addStep G R B := by
  classical
  have hk:=removes_keep_pivot_cluster G R C hCR hC v hv hr Subset.rfl inter_subset_left
  have hvN : v∈posNbhd G R v:=by simp [posNbhd]
  have hvB:=hk (mem_inter.mpr ⟨hvN,hv⟩)
  intro w hw
  exact mem_union_right _ (mem_filter.mpr ⟨hCR hw,
    good_transfer G R B C hCR hC v w hv hw (removes_clean G hr v hvB)⟩)

theorem run_captures_clean_cluster {R Z : Finset V} {L : List (Finset V × Finset V × Finset V)}
    (hrun : Run G R L Z) : ∀ C : Finset V,C⊆R→IsClean G R δ44 C→C.Nonempty→
      ∃ p∈L,C⊆p.2.1 := by
  induction hrun with
  | nil =>
    intro C hCR hC hne
    exact False.elim (not_nonempty_empty (hne.mono hCR))
  | @stop R hne hstop =>
    intro C hCR hC hneC
    obtain ⟨v,hv⟩:=hneC
    obtain ⟨B,hr,he⟩:=hstop v (hCR hv)
    have hc:=pivot_captures_cluster G R C hCR hC v hv B hr
    rw [he] at hc
    exact False.elim (notMem_empty v (hc hv))
  | @cluster R B A L Z v hv hremove hA hne hr ih =>
    intro C hCR hC hneC
    have hs:=add_preserves_cluster G R B C hCR hC (removes_clean G hremove)
    rw [←hA] at hs
    rcases hs with hcap|hdisj
    · exact ⟨(B,A,R),List.mem_cons_self,hcap⟩
    · have hCR' : C⊆R\A := by
        intro u hu
        exact mem_sdiff.mpr ⟨hCR hu,fun ha=>disjoint_left.mp hdisj hu ha⟩
      obtain ⟨p,hp,hcap⟩:=ih C hCR' (clean_restrict G (R\A) R C sdiff_subset hCR' δ44 hC) hneC
      exact ⟨p,List.mem_cons_of_mem _ hp,hcap⟩
end Queelius.Correlation

end

section
namespace Queelius.Correlation
open Finset CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem nbhd_inter_filter (R X : Finset V) (hXR : X⊆R) (v : V) :
    posNbhd G R v∩X=X.filter (fun u=>v=u ∨ G.Adj v u) := by
  ext u
  simp only [posNbhd,mem_inter,mem_insert,mem_filter]
  constructor
  · rintro ⟨h,hu⟩
    exact ⟨hu,h.elim (fun he=>Or.inl he.symm) (fun h=>Or.inr h.2)⟩
  · rintro ⟨hu,h⟩
    exact ⟨h.elim (fun he=>Or.inl he.symm) (fun ha=>Or.inr ⟨hXR hu,ha⟩),hu⟩

theorem neighbor_double_count (R B Y : Finset V) (hBR : B⊆R) (hYR : Y⊆R) :
    (∑ b∈B,((posNbhd G R b∩Y).card:ℝ))=∑ y∈Y,((posNbhd G R y∩B).card:ℝ) := by
  have h:=sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun b y=>b=y ∨ G.Adj b y) (s:=B) (t:=Y)
  have hN : (∑ b∈B,(posNbhd G R b∩Y).card)=∑ y∈Y,(posNbhd G R y∩B).card := by
    simp_rw [nbhd_inter_filter G R Y hYR,nbhd_inter_filter G R B hBR]
    simpa only [bipartiteAbove,bipartiteBelow,eq_comm,G.adj_comm] using h
  exact_mod_cast hN

theorem add_all_good (R B : Finset V) (hB : IsClean G R (3*δ44) B) :
    ∀ v∈addStep G R B,IsGood G R (7*δ44) B v := by
  intro v hv
  simp only [addStep,mem_union,mem_filter] at hv
  rcases hv with hb|⟨_,hg⟩
  · obtain ⟨h₁,h₂⟩:=hB v hb
    have hb0 : (0:ℝ)≤B.card:=Nat.cast_nonneg _
    constructor <;> norm_num [δ44] at h₁ h₂ ⊢ <;> linarith
  · exact hg

theorem added_card_bound (R B : Finset V) (hBR : B⊆R) (hB : IsClean G R (3*δ44) B) :
    ((addStep G R B).card:ℝ)≤(1+4*δ44)*(B.card:ℝ) := by
  classical
  let A:=addStep G R B
  let Y:=A\B
  have hBA : B⊆A:=subset_union_left
  have hAR : A⊆R:=add_subset G hBR
  have hYR : Y⊆R:=sdiff_subset.trans hAR
  have hYD : Y⊆R\B := by
    intro y hy
    exact mem_sdiff.mpr ⟨hYR hy,(mem_sdiff.mp hy).2⟩
  have hlo : (Y.card:ℝ)*((1-7*δ44)*(B.card:ℝ))≤∑ y∈Y,((posNbhd G R y∩B).card:ℝ) := by
    calc
      _=∑ _∈Y,(1-7*δ44)*(B.card:ℝ) := by simp
      _≤_ := sum_le_sum (fun y hy=>(add_all_good G R B hB y (mem_sdiff.mp hy).1).1)
  have hhi : (∑ b∈B,((posNbhd G R b∩Y).card:ℝ))≤(B.card:ℝ)*((3*δ44)*(B.card:ℝ)) := by
    calc
      _≤∑ _∈B,(3*δ44)*(B.card:ℝ) := by
        apply sum_le_sum
        intro b hb
        have hc : ((posNbhd G R b∩Y).card:ℝ)≤(posNbhd G R b∩(R\B)).card := by
          exact_mod_cast card_le_card (inter_subset_inter_left hYD)
        exact hc.trans (hB b hb).2
      _=_ := by simp
  rw [←neighbor_double_count G R B Y hBR hYR] at hlo
  have hzero : B=∅→A=∅ := by
    intro hb
    subst B
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hgood:=add_all_good G R ∅ hB v hv
    have hvR:=hAR hv
    have hself : v∈posNbhd G R v∩(R\∅):=mem_inter.mpr ⟨by simp [posNbhd],by simpa using hvR⟩
    have hc : (0:ℝ)<(posNbhd G R v∩(R\∅)).card := by exact_mod_cast card_pos.mpr ⟨v,hself⟩
    have hu:=hgood.2
    simp only [card_empty,Nat.cast_zero,mul_zero] at hu
    linarith
  change (A.card:ℝ)≤(1+4*δ44)*(B.card:ℝ)
  by_cases hb : B=∅
  · rw [hzero hb,hb]
    simp
  have hbpos : (0:ℝ)<B.card:=by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hb)
  have hy0 : (0:ℝ)≤Y.card:=Nat.cast_nonneg _
  have hs : (A.card:ℝ)=(B.card:ℝ)+(Y.card:ℝ) := by
    exact_mod_cast (card_sdiff_add_card_eq_card hBA).symm.trans (Nat.add_comm _ _)
  have hy : (Y.card:ℝ)≤4*δ44*(B.card:ℝ) := by
    norm_num [δ44] at hlo hhi ⊢
    nlinarith
  dsimp [A] at hs
  norm_num [δ44] at hy ⊢
  linarith

theorem add_is_clean (R B : Finset V) (hBR : B⊆R) (hB : IsClean G R (3*δ44) B) :
    IsClean G R (11*δ44) (addStep G R B) := by
  classical
  let A:=addStep G R B
  have hBA : B⊆A:=subset_union_left
  have hcard : (B.card:ℝ)≤A.card:=by exact_mod_cast card_le_card hBA
  have hub:=added_card_bound G R B hBR hB
  change (A.card:ℝ)≤(1+4*δ44)*(B.card:ℝ) at hub
  intro v hv
  obtain ⟨h₁,h₂⟩:=add_all_good G R B hB v hv
  have hlo : ((posNbhd G R v∩B).card:ℝ)≤(posNbhd G R v∩A).card := by
    exact_mod_cast card_le_card (inter_subset_inter_left hBA)
  have hhi : ((posNbhd G R v∩(R\A)).card:ℝ)≤(posNbhd G R v∩(R\B)).card := by
    exact_mod_cast card_le_card (inter_subset_inter_left (sdiff_subset_sdiff_right R hBA))
  have hb0 : (0:ℝ)≤B.card:=Nat.cast_nonneg _
  constructor <;> norm_num [δ44] at h₁ h₂ hub ⊢ <;> linarith
end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

def clusterFamily (D : Setoid V) : Finset (Finset V) := univ.image (classOf D)

theorem class_at_member (D : Setoid V) (C : Finset V) (hC : C∈clusterFamily D)
    (v : V) (hv : v∈C) : classOf D v=C := by
  obtain ⟨u,_,rfl⟩:=mem_image.mp hC
  have h : D.r u v:=by simpa [classOf] using hv
  exact (class_eq_of_related D h).symm

theorem cluster_pairwise_disjoint (D : Setoid V) :
    (↑(clusterFamily D) : Set (Finset V)).PairwiseDisjoint id := by
  intro C hC K hK hne
  obtain ⟨u,_,rfl⟩:=mem_image.mp hC
  obtain ⟨v,_,rfl⟩:=mem_image.mp hK
  apply classes_disjoint D u v
  intro h
  exact hne (class_eq_of_related D h)

theorem cluster_union (D : Setoid V) : (clusterFamily D).biUnion id=univ := by
  ext v
  simp only [mem_biUnion,mem_univ,iff_true]
  exact ⟨classOf D v,mem_image.mpr ⟨v,mem_univ _,rfl⟩,class_mem_self D v⟩

theorem sum_over_classes (D : Setoid V) (f : V → ℝ) :
    ∑C∈clusterFamily D,∑v∈C,f v=∑v,f v := by
  have h : (∑v∈(clusterFamily D).biUnion id,f v)=∑C∈clusterFamily D,∑v∈C,f v :=
    sum_biUnion (cluster_pairwise_disjoint D)
  simpa only [cluster_union] using h.symm

variable (G : SimpleGraph V) [DecidableRel G.Adj]
theorem bad_degree_mass (δ : ℝ) (D : Setoid V) (C : Finset V) (hC : C∈clusterFamily D) :
    (δ/3)*(C.card:ℝ)*((badVertices G δ C).card:ℝ) ≤
      ∑v∈badVertices G δ C,((relationNeighbors (IsMistake G D.r) v).card:ℝ) := by
  calc
    _ = ∑v∈badVertices G δ C,(δ/3)*(C.card:ℝ) := by simp [mul_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro v hv
      have he:=class_at_member D C hC v (mem_filter.mp hv).1
      have hb : v∈badVertices G δ (classOf D v) := by rwa [he]
      simpa only [he] using (bad_vertex_degree G δ D v hb).le

theorem bad_mass_le_total (δ : ℝ) (D : Setoid V) :
    (∑C∈clusterFamily D,∑v∈badVertices G δ C,((relationNeighbors (IsMistake G D.r) v).card:ℝ)) ≤
      ∑v,((relationNeighbors (IsMistake G D.r) v).card:ℝ) := by
  rw [←sum_over_classes D]
  apply sum_le_sum
  intro C _
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _=>Nat.cast_nonneg _)
end Queelius.Correlation

end

section
namespace Queelius.Correlation
open Finset CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_output_clean {R Z : Finset V} {L : List (Finset V × Finset V × Finset V)}
    (hrun : Run G R L Z) : ∀ p∈L,IsClean G p.2.2 (11*δ44) p.2.1 := by
  induction hrun with
  | nil => simp
  | stop => simp
  | @cluster R B A L Z v hv hremove hA hne hr ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · dsimp only
      rw [hA]
      exact add_is_clean G R B ((removes_subset G hremove).trans (nbhd_subset G hv))
        (removes_clean G hremove)
    · exact ih p hp

theorem run_theorem_seven (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G univ L Z) :
    (∀ v,2≤(classOf D v).card→∃ p∈L,classOf D v⊆p.2.1) ∧
      ∀ p∈L,IsClean G p.2.2 (11*δ44) p.2.1 := by
  refine ⟨?_,run_output_clean G hrun⟩
  intro v hv
  exact run_captures_clean_cluster G hrun (classOf D v) (subset_univ _) (hD v hv)
    ⟨v,class_mem_self D v⟩

theorem run_terminal_subset {R Z : Finset V} {L : List (Finset V × Finset V × Finset V)}
    (hrun : Run G R L Z) : Z⊆R := by
  induction hrun with
  | nil => exact Subset.rfl
  | stop => exact Subset.rfl
  | cluster hv hremove hA hne hr ih => exact ih.trans sdiff_subset

theorem run_terminal_disjoint_output {R Z : Finset V} {L : List (Finset V × Finset V × Finset V)}
    (hrun : Run G R L Z) : ∀ p∈L,Disjoint Z p.2.1 := by
  induction hrun with
  | nil => simp
  | stop => simp
  | @cluster R B A L Z v hv hremove hA hne hr ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · apply disjoint_left.mpr
      intro z hz ha
      exact (mem_sdiff.mp (run_terminal_subset G hr hz)).2 ha
    · exact ih p hp

theorem terminal_vertices_are_singletons (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G univ L Z) :
    Z⊆singletonsOf D := by
  intro v hv
  have hpos : 0<(classOf D v).card:=card_pos.mpr ⟨v,class_mem_self D v⟩
  have hsmall : (classOf D v).card<2 := by
    by_contra h
    obtain ⟨p,hp,hcap⟩:=(run_theorem_seven G D hD L Z hrun).1 v (by omega)
    exact disjoint_left.mp (run_terminal_disjoint_output G hrun p hp) hv (hcap (class_mem_self D v))
  simp only [singletonsOf,mem_filter,mem_univ,true_and]
  omega
end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def cleanupCuts (δ : ℝ) (D : Setoid V) (v : V) : Finset V :=
  univ.filter (fun u=>G.Adj v u ∧ D.r v u ∧ ¬(cleanupSetoid G δ D).r v u)

theorem cut_subset_class (δ : ℝ) (D : Setoid V) (v : V) :
    cleanupCuts G δ D v ⊆ classOf D v := by
  intro u hu
  simpa only [classOf,mem_filter,mem_univ,true_and] using (mem_filter.mp hu).2.2.1

theorem cut_subset_removed (δ : ℝ) (D : Setoid V) (v : V) (hv : keepVertex G δ D v) :
    cleanupCuts G δ D v ⊆ classOf D v\cleanCore G δ (classOf D v) := by
  intro u hu
  refine mem_sdiff.mpr ⟨cut_subset_class G δ D v hu,?_⟩
  intro hc
  have hr : D.r v u := (mem_filter.mp hu).2.2.1
  have hk : keepVertex G δ D u := by
    unfold keepVertex
    rw [←class_eq_of_related D hr]
    exact hc
  exact (mem_filter.mp hu).2.2.2 (Or.inr ⟨hr,hv,hk⟩)

theorem cut_degree_le_size (δ : ℝ) (D : Setoid V) (C : Finset V) (hC : C∈clusterFamily D)
    (v : V) (hv : v∈C) : ((cleanupCuts G δ D v).card:ℝ) ≤ C.card := by
  have h:=card_le_card (cut_subset_class G δ D v)
  rw [class_at_member D C hC v hv] at h
  exact_mod_cast h

theorem retained_cut_degree (δ : ℝ) (D : Setoid V) (C : Finset V) (hC : C∈clusterFamily D)
    (hsmall : ((badVertices G δ C).card:ℝ) ≤ (δ/3)*(C.card:ℝ))
    (v : V) (hv : v∈C) (hb : v∉badVertices G δ C) :
    ((cleanupCuts G δ D v).card:ℝ) ≤ (badVertices G δ C).card := by
  have he:=class_at_member D C hC v hv
  have hk : keepVertex G δ D v := by
    unfold keepVertex
    rw [he]
    simp only [cleanCore,if_pos hsmall]
    exact mem_sdiff.mpr ⟨hv,hb⟩
  have hs : cleanupCuts G δ D v ⊆ badVertices G δ C := by
    intro u hu
    have hh:=cut_subset_removed G δ D v hk hu
    rw [he] at hh
    simp only [cleanCore,if_pos hsmall,mem_sdiff] at hh
    tauto
  exact_mod_cast card_le_card hs

theorem small_cluster_cut_sum (δ : ℝ) (D : Setoid V) (C : Finset V) (hC : C∈clusterFamily D)
    (hsmall : ((badVertices G δ C).card:ℝ) ≤ (δ/3)*(C.card:ℝ)) :
    (∑v∈C,((cleanupCuts G δ D v).card:ℝ)) ≤ 2*((badVertices G δ C).card:ℝ)*(C.card:ℝ) := by
  let B:=badVertices G δ C
  have hBC : B⊆C:=filter_subset _ _
  have hh (v : V) (hv : v∈C) : ((cleanupCuts G δ D v).card:ℝ) ≤
      (B.card:ℝ)+(if v∈B then (C.card:ℝ) else 0) := by
    by_cases hb : v∈B
    · simp only [if_pos hb]
      have h:=cut_degree_le_size G δ D C hC v hv
      have hz : (0:ℝ) ≤ B.card:=Nat.cast_nonneg _
      linarith
    · simp only [if_neg hb,add_zero]
      exact retained_cut_degree G δ D C hC hsmall v hv hb
  calc
    _ ≤ ∑v∈C,((B.card:ℝ)+(if v∈B then (C.card:ℝ) else 0)) := sum_le_sum hh
    _ = 2*(B.card:ℝ)*(C.card:ℝ) := by
      rw [sum_add_distrib,←sum_filter]
      have hf : C.filter (fun v=>v∈B)=B := by ext v;simp only [mem_filter];exact ⟨And.right,fun h=>⟨hBC h,h⟩⟩
      rw [hf]
      simp only [sum_const,nsmul_eq_mul]
      ring

theorem cluster_cut_charge (δ : ℝ) (hd0 : 0 < δ) (hd1 : δ < 1)
    (D : Setoid V) (C : Finset V) (hC : C∈clusterFamily D) :
    (∑v∈C,((cleanupCuts G δ D v).card:ℝ)) ≤
      (9/δ^2)*(∑v∈badVertices G δ C,((relationNeighbors (IsMistake G D.r) v).card:ℝ)) := by
  let b : ℝ:=(badVertices G δ C).card
  let c : ℝ:=C.card
  let d : ℝ:=∑v∈badVertices G δ C,((relationNeighbors (IsMistake G D.r) v).card:ℝ)
  let z : ℝ:=∑v∈C,((cleanupCuts G δ D v).card:ℝ)
  have hb0 : 0 ≤ b:=Nat.cast_nonneg _
  have hc0 : 0 ≤ c:=Nat.cast_nonneg _
  have hd : (δ/3)*c*b ≤ d:=bad_degree_mass G δ D C hC
  have hz : z*δ^2 ≤ 9*d := by
    by_cases hsmall : b ≤ (δ/3)*c
    · have hs : z ≤ 2*b*c:=small_cluster_cut_sum G δ D C hC hsmall
      have hf : 2*δ^2 ≤ 3*δ:=by nlinarith
      have hmul:=mul_le_mul_of_nonneg_right hf (mul_nonneg hb0 hc0)
      have hsz:=mul_le_mul_of_nonneg_right hs (sq_nonneg δ)
      nlinarith
    · have hs : z ≤ c*c := by
        calc
          z ≤ ∑v∈C,c := sum_le_sum (fun v hv=>cut_degree_le_size G δ D C hC v hv)
          _ = c*c := by simp [c]
      have hh : (δ/3)*c ≤ b:=(lt_of_not_ge hsmall).le
      have hmul:=mul_le_mul_of_nonneg_left hh (mul_nonneg (by linarith : 0 ≤ δ/3) hc0)
      have hsz:=mul_le_mul_of_nonneg_right hs (sq_nonneg δ)
      nlinarith
  change z ≤ 9/δ^2*d
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sq_pos_of_pos hd0)).mpr hz
end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

def cutCount (Q : V→V→Prop) (A B : Finset V) : ℕ := ∑u∈A,(B.filter (Q u)).card

theorem cut_count_swap (Q : V→V→Prop) (hQ : Symmetric Q) (A B : Finset V) :
    cutCount Q A B=cutCount Q B A := by
  have he (u v : V) : Q u v↔Q v u:=⟨fun h=>hQ h,fun h=>hQ h⟩
  unfold cutCount
  simp only [card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro u _
  simp only [he u v]

theorem cut_count_partition (Q : V→V→Prop) (A B : Finset V) :
    cutCount Q A B+cutCount (fun u v=>¬Q u v) A B=A.card*B.card := by
  unfold cutCount
  rw [←sum_add_distrib]
  have h (u : V) : (B.filter (Q u)).card+(B.filter (fun v=>¬Q u v)).card=B.card:=
    card_filter_add_card_filter_not (Q u)
  simp_rw [h]
  simp

variable (G : SimpleGraph V) [DecidableRel G.Adj]
theorem clean_negative_degree (C R : Finset V) (hCR : C⊆R)
    (hc : IsClean G R (1/4) C) (u : V) (hu : u∈C) :
    ((C\posNbhd G R u).card:ℝ) ≤ (C.card:ℝ)/4 := by
  have h:= (hc u hu).1
  have hs:=card_split C (posNbhd G R u)
  rw [inter_comm C] at hs
  linarith

theorem clean_cut_negative_bound (C R A B : Finset V) (hCR : C⊆R)
    (hAC : A⊆C) (hBC : B⊆C) (hAB : Disjoint A B)
    (hc : IsClean G R (1/4) C) :
    (cutCount (fun u v=>¬G.Adj u v) A B:ℝ) ≤ (C.card:ℝ)/4*(A.card:ℝ) := by
  have h (u : V) (hu : u∈A) : ((B.filter (fun v=>¬G.Adj u v)).card:ℝ) ≤ (C.card:ℝ)/4 := by
    have hs : B.filter (fun v=>¬G.Adj u v) ⊆ C\posNbhd G R u := by
      intro v hv
      have hb:=(mem_filter.mp hv).1
      have hne : v≠u := by intro he;subst v;exact disjoint_left.mp hAB hu hb
      apply mem_sdiff.mpr
      refine ⟨hBC hb,?_⟩
      simp only [posNbhd,mem_insert,mem_filter]
      intro hz
      rcases hz with hz|hz
      · exact hne hz
      · exact (mem_filter.mp hv).2 hz.2
    exact (show ((B.filter (fun v=>¬G.Adj u v)).card:ℝ)≤(C\posNbhd G R u).card by exact_mod_cast card_le_card hs).trans
      (clean_negative_degree G C R hCR hc u (hAC hu))
  calc
    _ = ∑u∈A,((B.filter (fun v=>¬G.Adj u v)).card:ℝ) := by simp [cutCount]
    _ ≤ ∑_u∈A,(C.card:ℝ)/4 := sum_le_sum h
    _ = _ := by simp [mul_comm]

theorem clean_cut_dominance (C R A B : Finset V) (hCR : C⊆R)
    (hAB : Disjoint A B) (hunion : A∪B=C) (hc : IsClean G R (1/4) C) :
    cutCount (fun u v=>¬G.Adj u v) A B ≤ cutCount G.Adj A B := by
  have hAC : A⊆C:=by rw [←hunion];exact subset_union_left
  have hBC : B⊆C:=by rw [←hunion];exact subset_union_right
  have hcard : (C.card:ℝ)=(A.card:ℝ)+(B.card:ℝ) := by rw [←hunion,card_union_of_disjoint hAB];push_cast;rfl
  have hpartition : (cutCount G.Adj A B:ℝ)+(cutCount (fun u v=>¬G.Adj u v) A B:ℝ)=(A.card:ℝ)*(B.card:ℝ) := by exact_mod_cast cut_count_partition G.Adj A B
  have hsmall (A B : Finset V) (ha : A⊆C) (hb : B⊆C) (hab : Disjoint A B)
      (hsize : A.card≤B.card) (hcard : (C.card:ℝ)=(A.card:ℝ)+(B.card:ℝ)) :
      2*(cutCount (fun u v=>¬G.Adj u v) A B:ℝ)≤(A.card:ℝ)*(B.card:ℝ) := by
    have h:=clean_cut_negative_bound G C R A B hCR ha hb hab hc
    have hs : (A.card:ℝ)≤B.card:=by exact_mod_cast hsize
    nlinarith [mul_nonneg (Nat.cast_nonneg A.card) (sub_nonneg.mpr hs)]
  rcases le_total A.card B.card with hs|hs
  · have h:=hsmall A B hAC hBC hAB hs hcard
    exact_mod_cast (show (cutCount (fun u v=>¬G.Adj u v) A B:ℝ)≤cutCount G.Adj A B by linarith)
  · have h:=hsmall B A hBC hAC hAB.symm hs (by linarith)
    rw [cut_count_swap (fun u v=>¬G.Adj u v) (fun _ _ h hp=>h hp.symm) B A] at h
    exact_mod_cast (show (cutCount (fun u v=>¬G.Adj u v) A B:ℝ)≤cutCount G.Adj A B by nlinarith)
end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

def clusterSize (D : Setoid V) (u : V) : ℝ := (classOf D u).card

theorem cluster_size_pos (D : Setoid V) (u : V) : 0 < clusterSize D u := by
  unfold clusterSize
  exact_mod_cast card_pos.mpr ⟨u,class_mem_self D u⟩

variable (G : SimpleGraph V) [DecidableRel G.Adj]
def positiveTriple (D : Setoid V) (a b c : V) : ℝ :=
  if G.Adj a b ∧ ¬D.r a b ∧ D.r a c ∧ G.Adj a c ∧ ¬G.Adj b c
    then 1/(clusterSize D a+clusterSize D b) else 0

theorem positive_triple_nonneg (D : Setoid V) (a b c : V) : 0 ≤ positiveTriple G D a b c := by
  unfold positiveTriple
  split
  · exact div_nonneg zero_le_one (add_pos (cluster_size_pos D a) (cluster_size_pos D b)).le
  · exact le_rfl

theorem positive_triple_erroneous (D : Setoid V) (a b c : V)
    (h : positiveTriple G D a b c≠0) : IsErroneous G {a,b,c} := by
  have he : G.Adj a b ∧ ¬D.r a b ∧ D.r a c ∧ G.Adj a c ∧ ¬G.Adj b c := by
    by_contra hn;exact h (by simp [positiveTriple,hn])
  refine ⟨a,b,c,rfl,he.1.ne,he.2.2.2.1.ne,?_,he.1,he.2.2.2.1,he.2.2.2.2⟩
  intro hh;subst c;exact he.2.1 he.2.2.1

theorem positive_third_bound (D : Setoid V) (a b : V) :
    (∑c,positiveTriple G D a b c) ≤ clusterSize D a/(clusterSize D a+clusterSize D b) := by
  have hd : 0 < clusterSize D a+clusterSize D b:=add_pos (cluster_size_pos D a) (cluster_size_pos D b)
  calc
    _ ≤ ∑c,if D.r a c then 1/(clusterSize D a+clusterSize D b) else 0 := by
      apply sum_le_sum;intro c _
      unfold positiveTriple
      split_ifs <;> simp_all <;> positivity
    _ = _ := by simp [←sum_filter,clusterSize,classOf,div_eq_mul_inv]

theorem clean_external_degree (δ : ℝ) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (u : V) :
    ((univ.filter (fun v=>G.Adj u v ∧ ¬D.r u v)).card:ℝ) ≤ δ*clusterSize D u := by
  have hh:=(hD u u (class_mem_self D u)).2
  have he : posNbhd G univ u∩(univ\classOf D u)=univ.filter (fun v=>G.Adj u v ∧ ¬D.r u v) := by
    ext v
    simp only [posNbhd,classOf,mem_inter,mem_insert,mem_filter,mem_univ,true_and,mem_sdiff]
    constructor
    · rintro ⟨hv,hn⟩
      rcases hv with hv|hv
      · subst v;exact False.elim (hn (D.refl u))
      · exact ⟨hv,hn⟩
    · intro h;exact ⟨Or.inr h.1,h.2⟩
  simpa only [he,clusterSize] using hh

theorem positive_middle_bound (δ : ℝ) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (u v : V) :
    (∑b,positiveTriple G D u b v) ≤ δ := by
  have hs:=cluster_size_pos D u
  have hrow : (∑b,positiveTriple G D u b v) ≤
      ((univ.filter (fun b=>G.Adj u b ∧ ¬D.r u b)).card:ℝ)/clusterSize D u := by
    calc
      _ ≤ ∑b,if G.Adj u b ∧ ¬D.r u b then 1/clusterSize D u else 0 := by
        apply sum_le_sum;intro b _
        unfold positiveTriple
        split_ifs with h hh hh
        · exact div_le_div_of_nonneg_left zero_le_one hs (le_add_of_nonneg_right (cluster_size_pos D b).le)
        · exact False.elim (hh ⟨h.1,h.2.1⟩)
        · positivity
        · exact le_rfl
      _ = _ := by simp [←sum_filter,div_eq_mul_inv]
  exact hrow.trans ((div_le_iff₀ hs).mpr (by nlinarith [clean_external_degree G δ D hD u]))

theorem positive_first_bound (δ : ℝ) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (u v : V) :
    (∑a,positiveTriple G D a u v) ≤ δ := by
  have hs:=cluster_size_pos D u
  have hrow : (∑a,positiveTriple G D a u v) ≤
      ((univ.filter (fun a=>G.Adj u a ∧ ¬D.r u a)).card:ℝ)/clusterSize D u := by
    calc
      _ ≤ ∑a,if G.Adj u a ∧ ¬D.r u a then 1/clusterSize D u else 0 := by
        apply sum_le_sum;intro a _
        unfold positiveTriple
        split_ifs with h hh hh
        · exact div_le_div_of_nonneg_left zero_le_one hs (le_add_of_nonneg_left (cluster_size_pos D a).le)
        · exact False.elim (hh ⟨h.1.symm,fun hr=>h.2.1 (D.symm hr)⟩)
        · positivity
        · exact le_rfl
      _ = _ := by simp [←sum_filter,div_eq_mul_inv]
  exact hrow.trans ((div_le_iff₀ hs).mpr (by nlinarith [clean_external_degree G δ D hD u]))

theorem positive_packing (δ : ℝ) (hd : δ ≤ 1/4) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) : IsFracPacking G (triangleMass (positiveTriple G D)) := by
  apply packing_of_triple_weights G _ (positive_triple_nonneg G D) (positive_triple_erroneous G D)
  intro u v huv
  by_cases hg:G.Adj u v
  · have hz1 : (∑a,positiveTriple G D a u v)=0:=by simp [positiveTriple,hg]
    have hz2 : (∑a,positiveTriple G D a v u)=0:=by simp [positiveTriple,hg.symm]
    rw [hz1,hz2,add_zero,add_zero]
    by_cases hr:D.r u v
    · have hz3 : (∑c,positiveTriple G D u v c)=0:=by simp [positiveTriple,hr]
      have hz4 : (∑c,positiveTriple G D v u c)=0:=by simp [positiveTriple,D.symm hr]
      rw [hz3,hz4]
      linarith [positive_middle_bound G δ D hD u v,positive_middle_bound G δ D hD v u]
    · have hz3 : (∑b,positiveTriple G D u b v)=0:=by simp [positiveTriple,hr]
      have hz4 : (∑b,positiveTriple G D v b u)=0:=by
        have hh : ¬D.r v u:=fun h=>hr (D.symm h)
        simp [positiveTriple,hh]
      rw [hz3,hz4,add_zero,add_zero]
      have h1:=positive_third_bound G D u v
      have h2:=positive_third_bound G D v u
      have hden : clusterSize D u+clusterSize D v≠0:=(add_pos (cluster_size_pos D u) (cluster_size_pos D v)).ne'
      rw [add_comm (clusterSize D v)] at h2
      have hh : clusterSize D u/(clusterSize D u+clusterSize D v)+clusterSize D v/(clusterSize D u+clusterSize D v)=1:=by rw [←add_div,div_self hden]
      linarith
  · have hgr : ¬G.Adj v u:=fun h=>hg h.symm
    have hz1 : (∑c,positiveTriple G D u v c)=0:=by simp [positiveTriple,hg]
    have hz2 : (∑c,positiveTriple G D v u c)=0:=by simp [positiveTriple,hgr]
    have hz3 : (∑b,positiveTriple G D u b v)=0:=by simp [positiveTriple,hg]
    have hz4 : (∑b,positiveTriple G D v b u)=0:=by simp [positiveTriple,hgr]
    rw [hz1,hz2,hz3,hz4]
    linarith [positive_first_bound G δ D hD u v,positive_first_bound G δ D hD v u]
end Queelius.Correlation

end

section
namespace Queelius.Correlation.Controls
open Finset CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem complete_neighborhood (R : Finset V) (v : V) (hv : v∈R) :
    posNbhd (⊤ : SimpleGraph V) R v=R := by
  ext u
  simp only [posNbhd,mem_insert,mem_filter,SimpleGraph.top_adj]
  constructor
  · rintro (rfl|⟨hu,_⟩)
    · exact hv
    · exact hu
  · intro hu
    by_cases h : u=v
    · exact Or.inl h
    · exact Or.inr ⟨hu,Ne.symm h⟩

theorem complete_good (R : Finset V) (v : V) (hv : v∈R) (d : ℝ) (hd : 0≤d) :
    IsGood (⊤ : SimpleGraph V) R d R v := by
  unfold IsGood
  rw [complete_neighborhood R v hv]
  simp only [inter_self,sdiff_self,bot_eq_empty,inter_empty,card_empty,Nat.cast_zero]
  have hc : (0:ℝ)≤R.card:=Nat.cast_nonneg _
  constructor <;> nlinarith [mul_nonneg hd hc]

theorem complete_removal_keeps_all (R B : Finset V) (h : Removes (⊤ : SimpleGraph V) R R B) : B=R := by
  cases h with
  | done => rfl
  | drop hx hbad h => exact False.elim (hbad (complete_good R _ hx _ (by norm_num [δ44])))

theorem adding_to_whole_set (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V) :
    addStep G R R=R := by
  classical
  exact union_eq_left.mpr (filter_subset _ _)

theorem complete_one_cluster_run (R : Finset V) (hR : R.Nonempty) :
    Run (⊤ : SimpleGraph V) R [(R,R,R)] ∅ := by
  obtain ⟨v,hv⟩:=hR
  have hr : Removes (⊤ : SimpleGraph V) R (posNbhd ⊤ R v) R := by
    rw [complete_neighborhood R v hv]
    exact Removes.done (fun u hu=>complete_good R u hu _ (by norm_num [δ44]))
  exact Run.cluster hv hr (adding_to_whole_set ⊤ R).symm ⟨v,hv⟩ (by simpa using (Run.nil (G:= (⊤ : SimpleGraph V))))

theorem empty_seed_adds_nothing (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V) :
    addStep G R ∅=∅ := by
  have h:=added_card_bound G R ∅ (empty_subset _) (by simp [IsClean])
  simpa using h

theorem empty_graph_pair_not_clean :
    ¬IsClean (⊥ : SimpleGraph (Fin 2)) univ δ44 univ := by
  intro h
  have h0:=(h 0 (mem_univ _)).1
  norm_num [posNbhd,δ44] at h0

theorem pivot_is_inserted_even_outside (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    posNbhd G ∅ v={v} := by simp [posNbhd]
end Queelius.Correlation.Controls

end

section
namespace Queelius.Correlation
open Finset CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem comparison_relation_preserved (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G univ L Z)
    (u v : V) (h : D.r u v) : sameCluster L u v := by
  classical
  by_cases huv : u=v
  · exact Or.inl huv
  have hu : u∈classOf D u:=class_mem_self D u
  have hv : v∈classOf D u:=by simpa only [classOf,mem_filter,mem_univ,true_and] using h
  have hsub : {u,v}⊆classOf D u:=by intro x hx;simp only [mem_insert,mem_singleton] at hx;rcases hx with rfl|rfl <;> assumption
  have hc : 2≤(classOf D u).card:=by simpa [huv] using card_le_card hsub
  obtain ⟨p,hp,hcap⟩:=(run_theorem_seven G D hD L Z hrun).1 u hc
  exact Or.inr ⟨p,hp,hcap hu,hcap hv⟩

theorem positive_mistakes_bound (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G univ L Z) :
    posMistakes G (sameCluster L)≤posMistakes G D.r := by
  classical
  apply card_le_card
  intro e he
  simp only [mem_filter,mem_univ,true_and] at he ⊢
  obtain ⟨u,v,he,huv,hg,hn⟩:=he
  exact ⟨u,v,he,huv,hg,fun hd=>hn (comparison_relation_preserved G D hD L Z hrun u v hd)⟩

theorem terminal_relation_eq {R Z : Finset V} {L : List (Finset V × Finset V × Finset V)}
    (hrun : Run G R L Z) (u v : V) (hz : u∈Z ∨ v∈Z) : sameCluster L u v↔u=v := by
  constructor
  · rintro (he|⟨p,hp,hu,hv⟩)
    · exact he
    · rcases hz with hz|hz
      · exact False.elim (disjoint_left.mp (run_terminal_disjoint_output G hrun p hp) hz hu)
      · exact False.elim (disjoint_left.mp (run_terminal_disjoint_output G hrun p hp) hz hv)
  · exact Or.inl

theorem external_mistakes_bound (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G univ L Z) :
    extMistakes G (sameCluster L) Z≤extMistakes G D.r (singletonsOf D) := by
  classical
  apply card_le_card
  intro e he
  simp only [mem_filter,mem_univ,true_and] at he ⊢
  obtain ⟨u,v,he,hm,hz⟩:=he
  have hn : ¬sameCluster L u v := fun h=>hm.1 ((terminal_relation_eq G hrun u v hz).mp h)
  have hg : G.Adj u v:=hm.2.elim And.left (fun h=>False.elim (hn h.2))
  have hnd : ¬D.r u v:=fun h=>hn (comparison_relation_preserved G D hD L Z hrun u v h)
  have hsingle:=terminal_vertices_are_singletons G D hD L Z hrun
  exact ⟨u,v,he,⟨hm.1,Or.inl ⟨hg,hnd⟩⟩,hz.elim (fun h=>Or.inl (hsingle h)) (fun h=>Or.inr (hsingle h))⟩

theorem run_lemma_eleven (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G univ L Z) :
    extMistakes G (sameCluster L) Z≤extMistakes G D.r (singletonsOf D) ∧
      posMistakes G (sameCluster L)≤posMistakes G D.r :=
  ⟨external_mistakes_bound G D hD L Z hrun,positive_mistakes_bound G D hD L Z hrun⟩
end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cleanup_degree_increase (δ : ℝ) (D : Setoid V) (v : V) :
    ((relationNeighbors (IsMistake G (cleanupSetoid G δ D).r) v).card:ℝ) ≤
      ((relationNeighbors (IsMistake G D.r) v).card:ℝ)+((cleanupCuts G δ D v).card:ℝ) := by
  have hs : relationNeighbors (IsMistake G (cleanupSetoid G δ D).r) v ⊆
      relationNeighbors (IsMistake G D.r) v ∪ cleanupCuts G δ D v := by
    intro u hu
    have hm:=(mem_filter.mp hu).2
    rcases hm.2 with ⟨hg,hn⟩|⟨hg,hr⟩
    · by_cases hd : D.r v u
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hg,hd,hn⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hm.1,Or.inl ⟨hg,hd⟩⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hm.1,Or.inr ⟨hg,cleanup_refines G δ D hr⟩⟩)
  exact_mod_cast (card_le_card hs).trans (card_union_le _ _)

theorem cleanup_cut_sum (δ : ℝ) (hd0 : 0 < δ) (hd1 : δ < 1) (D : Setoid V) :
    (∑v,((cleanupCuts G δ D v).card:ℝ)) ≤
      (9/δ^2)*(∑v,((relationNeighbors (IsMistake G D.r) v).card:ℝ)) := by
  calc
    _ = ∑C∈clusterFamily D,∑v∈C,((cleanupCuts G δ D v).card:ℝ) := (sum_over_classes D _).symm
    _ ≤ ∑C∈clusterFamily D,(9/δ^2)*(∑v∈badVertices G δ C,((relationNeighbors (IsMistake G D.r) v).card:ℝ)) :=
      sum_le_sum (fun C hC=>cluster_cut_charge G δ hd0 hd1 D C hC)
    _ = (9/δ^2)*(∑C∈clusterFamily D,∑v∈badVertices G δ C,((relationNeighbors (IsMistake G D.r) v).card:ℝ)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (bad_mass_le_total G δ D) (div_nonneg (by norm_num) (sq_nonneg δ))

theorem cleanup_cost_bound (δ : ℝ) (hd0 : 0 < δ) (hd1 : δ < 1) (D : Setoid V) :
    (mistakes G (cleanupSetoid G δ D).r:ℝ) ≤ (9/δ^2+1)*(mistakes G D.r:ℝ) := by
  have hsum := sum_le_sum (s:=univ) (fun v _=>cleanup_degree_increase G δ D v)
  rw [sum_add_distrib] at hsum
  have hcuts:=cleanup_cut_sum G δ hd0 hd1 D
  have hnew : (∑v,((relationNeighbors (IsMistake G (cleanupSetoid G δ D).r) v).card:ℝ))=
      2*(mistakes G (cleanupSetoid G δ D).r:ℝ) := by exact_mod_cast mistake_degree_sum G (cleanupSetoid G δ D)
  have hold : (∑v,((relationNeighbors (IsMistake G D.r) v).card:ℝ))=2*(mistakes G D.r:ℝ) := by
    exact_mod_cast mistake_degree_sum G D
  rw [hnew,hold] at hsum
  rw [hold] at hcuts
  nlinarith

theorem cleanup_all (δ : ℝ) (hd0 : 0 < δ) (hd1 : δ < 1) (D : Setoid V) :
    ∃D':Setoid V,NonsingletonClean G δ D' ∧
      (mistakes G D'.r:ℝ) ≤ (9/δ^2+1)*(mistakes G D.r:ℝ) :=
  ⟨cleanupSetoid G δ D,cleanup_nonsingleton_clean G δ hd0.le hd1.le D,
    cleanup_cost_bound G δ hd0 hd1 D⟩
end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cut_across_partition (D : Setoid V) (Q : V→V→Prop) (C : Finset V) :
    (∑K∈clusterFamily D,(cutCount Q (C∩K) (C\K):ℝ))=
      (cutCount (fun u v=>Q u v ∧ ¬D.r u v) C C:ℝ) := by
  let f : V→ℝ:=fun u=>if u∈C then ((C.filter (fun v=>Q u v ∧ ¬D.r u v)).card:ℝ) else 0
  have he (K : Finset V) (hK : K∈clusterFamily D) :
      (cutCount Q (C∩K) (C\K):ℝ)=∑u∈K,f u := by
    have hset : C∩K=K.filter (fun u=>u∈C):=by ext u;simp [and_comm]
    simp only [cutCount,Nat.cast_sum,hset,sum_filter]
    apply sum_congr rfl
    intro u hu
    dsimp [f]
    by_cases huc:u∈C
    · rw [if_pos huc,if_pos huc]
      have hclass:=class_at_member D K hK u hu
      have hv (v : V) : D.r u v↔v∈K := by rw [←hclass];simp [classOf]
      congr 2
      ext v
      simp [hv,and_assoc,and_comm,and_left_comm]
    · simp [huc]
  calc
    _ = ∑K∈clusterFamily D,∑u∈K,f u := sum_congr rfl he
    _ = ∑u,f u := sum_over_classes D f
    _ = _ := by simp only [f,←sum_filter,filter_mem_eq_inter,univ_inter,cutCount,Nat.cast_sum]

variable (G : SimpleGraph V) [DecidableRel G.Adj]
theorem clean_cross_negative_le_positive (C R : Finset V) (hCR : C⊆R)
    (hc : IsClean G R (1/4) C) (D : Setoid V) :
    cutCount (fun u v=>¬G.Adj u v ∧ ¬D.r u v) C C ≤
      cutCount (fun u v=>G.Adj u v ∧ ¬D.r u v) C C := by
  have h : (∑K∈clusterFamily D,(cutCount (fun u v=>¬G.Adj u v) (C∩K) (C\K):ℝ))≤
      ∑K∈clusterFamily D,(cutCount G.Adj (C∩K) (C\K):ℝ) := by
    apply sum_le_sum
    intro K _
    exact_mod_cast clean_cut_dominance G C R (C∩K) (C\K) hCR disjoint_inf_sdiff
      (by ext v;simp only [mem_union,mem_inter,mem_sdiff];tauto) hc
  rw [cut_across_partition,cut_across_partition] at h
  exact_mod_cast h

theorem internal_cost_identity (C : Finset V) (D : Setoid V) :
    cutCount (fun u v=>u≠v ∧ ¬G.Adj u v) C C+
      cutCount (fun u v=>G.Adj u v ∧ ¬D.r u v) C C =
    cutCount (IsMistake G D.r) C C+
      cutCount (fun u v=>¬G.Adj u v ∧ ¬D.r u v) C C := by
  simp only [cutCount,card_eq_sum_ones,sum_filter]
  rw [←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro u _
  rw [←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro v _
  by_cases he:u=v
  · subst v;simp [IsMistake,D.refl]
  · by_cases hg:G.Adj u v <;> by_cases hd:D.r u v <;> simp [IsMistake,he,hg,hd]

theorem clean_internal_cost (C R : Finset V) (hCR : C⊆R)
    (hc : IsClean G R (1/4) C) (D : Setoid V) :
    cutCount (fun u v=>u≠v ∧ ¬G.Adj u v) C C ≤ cutCount (IsMistake G D.r) C C := by
  have h:=clean_cross_negative_le_positive G C R hCR hc D
  have hi:=internal_cost_identity G C D
  omega
end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem guarded_global_count (Q : V→V→Prop) (A B : Finset V) :
    cutCount (fun u v=>u∈A ∧ v∈B ∧ Q u v) univ univ=cutCount Q A B := by
  have hi (u : V) : (univ.filter (fun v=>u∈A ∧ v∈B ∧ Q u v)).card=
      if u∈A then (B.filter (Q u)).card else 0 := by
    by_cases hu:u∈A
    · simp only [hu,true_and,if_true]
      congr 1
      ext v;simp
    · simp [hu]
  unfold cutCount
  simp_rw [hi]
  rw [←sum_filter]
  simp

theorem global_count_subadd (Q P H : V→V→Prop) (h : ∀u v,Q u v→P u v ∨ H u v) :
    cutCount Q univ univ ≤ cutCount P univ univ+cutCount H univ univ := by
  unfold cutCount
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro u _
  have hs : univ.filter (Q u)⊆univ.filter (P u)∪univ.filter (H u) := by
    intro v hv
    rcases h u v (mem_filter.mp hv).2 with hp|hh
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hp⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hh⟩)
  exact (card_le_card hs).trans (card_union_le _ _)

theorem cut_second_mono (Q : V→V→Prop) (A B R : Finset V) (h : B⊆R) :
    cutCount Q A B ≤ cutCount Q A R := by
  apply sum_le_sum
  intro u _
  exact card_le_card (filter_subset_filter _ h)

theorem cut_diagonal_partition_le (Q : V→V→Prop) (A R : Finset V) (h : A⊆R) :
    cutCount Q A A+cutCount Q (R\A) (R\A) ≤ cutCount Q R R := by
  have h1:=cut_second_mono Q A A R h
  have h2:=cut_second_mono Q (R\A) (R\A) R sdiff_subset
  have hd : Disjoint A (R\A):=by
    apply disjoint_left.mpr
    intro u hu hv
    exact (mem_sdiff.mp hv).2 hu
  have he : A∪(R\A)=R:=union_sdiff_of_subset h
  have hh : cutCount Q A R+cutCount Q (R\A) R=cutCount Q R R := by
    unfold cutCount
    rw [←sum_union hd,he]
  omega

theorem global_count_degree (Q : V→V→Prop) (hs : Symmetric Q) (hi : ∀v,¬Q v v) :
    cutCount Q univ univ=2*(relationPairs Q).card := by
  exact relation_degree_sum Q hs hi
end Queelius.Correlation

end

section
namespace CorrClustBBC.Cautious
theorem corollary_10 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G Finset.univ L Z) :
    ∀ p ∈ L, ∀ u ∈ p.1, ∀ v ∈ p.1, 2 ≤ (classOf D u).card → 2 ≤ (classOf D v).card →
      D.r u v := by
  exact Queelius.Correlation.run_removal_separation G D hD L Z hrun
end CorrClustBBC.Cautious

namespace CorrClustBBC.Cautious
theorem theorem_7 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G Finset.univ L Z) :
    (∀ v, 2 ≤ (classOf D v).card → ∃ p ∈ L, classOf D v ⊆ p.2.1) ∧
      ∀ p ∈ L, IsClean G p.2.2 (11 * δ44) p.2.1 := by
  exact Queelius.Correlation.run_theorem_seven G D hD L Z hrun
end CorrClustBBC.Cautious

namespace CorrClustBBC.Cautious
theorem lemma_11 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Setoid V) (hD : NonsingletonClean G δ44 D)
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G Finset.univ L Z) :
    extMistakes G (sameCluster L) Z ≤ extMistakes G D.r (singletonsOf D) ∧
      posMistakes G (sameCluster L) ≤ posMistakes G D.r := by
  exact Queelius.Correlation.run_lemma_eleven G D hD L Z hrun
end CorrClustBBC.Cautious

end

section
noncomputable section
namespace Queelius.Correlation.Controls
open Finset Classical CorrClustBBC.Cautious

theorem path_good_zero (v : Fin 3) : IsGood pathGraph univ 0 univ v ↔ v=0 := by
  have hc : (posNbhd pathGraph univ v).card=if v=0 then 3 else 2 := by
    fin_cases v <;> decide
  simp only [IsGood,inter_univ,sdiff_self,bot_eq_empty,inter_empty,card_empty,Nat.cast_zero,card_univ,Fintype.card_fin]
  rw [hc]
  by_cases h : v=0 <;> norm_num [h]

theorem path_bad_at_zero : badVertices pathGraph 0 univ=({1,2}:Finset (Fin 3)) := by
  ext v
  rw [badVertices,mem_filter]
  simp only [mem_univ,true_and,zero_div,path_good_zero]
  fin_cases v <;> decide

theorem path_core_at_zero : cleanCore pathGraph 0 univ=∅ := by
  norm_num [cleanCore,path_bad_at_zero]

theorem path_cleanup_zero_discrete : cleanupSetoid pathGraph 0 (⊤:Setoid (Fin 3))=⊥ := by
  ext u v
  change (u=v ∨ ((⊤:Setoid (Fin 3)).r u v ∧ keepVertex pathGraph 0 ⊤ u ∧ keepVertex pathGraph 0 ⊤ v)) ↔ u=v
  simp [keepVertex,classOf,path_core_at_zero]

theorem zero_parameter_cost_failure :
    ¬(mistakes pathGraph (cleanupSetoid pathGraph 0 (⊤:Setoid (Fin 3))).r:ℝ) ≤
      (9/(0:ℝ)^2+1)*(mistakes pathGraph (⊤:Setoid (Fin 3)).r:ℝ) := by
  rw [path_cleanup_zero_discrete]
  change ¬(mistakes pathGraph (fun u v=>u=v):ℝ) ≤ (9/(0:ℝ)^2+1)*(mistakes pathGraph (fun _ _=>True):ℝ)
  rw [discrete_mistakes,universal_mistakes]
  norm_num

theorem path_degree_double_count :
    ∑v:Fin 3,(relationNeighbors (IsMistake pathGraph (⊤:Setoid (Fin 3)).r) v).card=2 := by
  rw [mistake_degree_sum]
  change 2*mistakes pathGraph (fun _ _=>True)=2
  rw [universal_mistakes]

def triangleAndIsolate : SimpleGraph (Fin 4) where
  Adj u v := u≠v ∧ u≠3 ∧ v≠3
  symm := ⟨by intro u v h;exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro u h;exact h.1 rfl⟩
instance : DecidableRel triangleAndIsolate.Adj := fun u v=>inferInstanceAs (Decidable (u≠v ∧ u≠3 ∧ v≠3))

theorem triangle_isolate_good (v : Fin 4) :
    IsGood triangleAndIsolate univ ((3/4)/3) univ v ↔ v≠3 := by
  have hc : (posNbhd triangleAndIsolate univ v).card=if v=3 then 1 else 3 := by
    fin_cases v <;> decide
  simp only [IsGood,inter_univ,sdiff_self,bot_eq_empty,inter_empty,card_empty,Nat.cast_zero,card_univ,Fintype.card_fin]
  rw [hc]
  by_cases h : v=3 <;> norm_num [h]

theorem equality_threshold_bad :
    badVertices triangleAndIsolate (3/4) univ=({3}:Finset (Fin 4)) := by
  ext v
  rw [badVertices,mem_filter]
  simp only [mem_univ,true_and,triangle_isolate_good,not_not,mem_singleton]

theorem equality_threshold_retains_core :
    cleanCore triangleAndIsolate (3/4) univ=({0,1,2}:Finset (Fin 4)) := by
  unfold cleanCore
  rw [equality_threshold_bad]
  norm_num
  ext v
  fin_cases v <;> decide

theorem retained_core_clean :
    IsClean triangleAndIsolate univ (3/4) ({0,1,2}:Finset (Fin 4)) := by
  rw [←equality_threshold_retains_core]
  exact core_clean _ _ (by norm_num) (by norm_num) _

theorem removed_isolate_singleton :
    classOf (cleanupSetoid triangleAndIsolate (3/4) (⊤:Setoid (Fin 4))) 3={3} := by
  apply cleanup_class_removed
  simp [keepVertex,classOf,equality_threshold_retains_core]
end Queelius.Correlation.Controls

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def negativeTriple (D : Setoid V) (a b c : V) : ℝ :=
  if D.r a b ∧ D.r a c ∧ G.Adj a b ∧ G.Adj a c ∧ b≠c ∧ ¬G.Adj b c
    then 1/(2*clusterSize D a) else 0

theorem negative_triple_nonneg (D : Setoid V) (a b c : V) : 0 ≤ negativeTriple G D a b c := by
  unfold negativeTriple
  split
  · exact div_nonneg zero_le_one (mul_pos (by norm_num) (cluster_size_pos D a)).le
  · exact le_rfl

theorem negative_triple_erroneous (D : Setoid V) (a b c : V)
    (h : negativeTriple G D a b c≠0) : IsErroneous G {a,b,c} := by
  have he : D.r a b ∧ D.r a c ∧ G.Adj a b ∧ G.Adj a c ∧ b≠c ∧ ¬G.Adj b c := by
    by_contra hn;exact h (by simp [negativeTriple,hn])
  exact ⟨a,b,c,rfl,he.2.2.1.ne,he.2.2.2.1.ne,he.2.2.2.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2.2⟩

theorem cluster_size_related (D : Setoid V) {u v : V} (h : D.r u v) :
    clusterSize D u=clusterSize D v := by
  unfold clusterSize
  rw [class_eq_of_related D h]

theorem clean_parameter_nonneg (δ : ℝ) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (u : V) : 0 ≤ δ := by
  have h:=clean_external_degree G δ D hD u
  nlinarith [cluster_size_pos D u,Nat.cast_nonneg (α:=ℝ) (univ.filter (fun v=>G.Adj u v ∧ ¬D.r u v)).card]

def negativeNeighbors (D : Setoid V) (u : V) : Finset V :=
  univ.filter (fun v=>v≠u ∧ ¬G.Adj u v ∧ D.r u v)

theorem clean_negative_neighbors (δ : ℝ) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (u : V) :
    ((negativeNeighbors G D u).card:ℝ) ≤ δ*clusterSize D u := by
  have he : negativeNeighbors G D u=classOf D u\posNbhd G univ u := by
    ext v
    simp [negativeNeighbors,classOf,posNbhd,and_assoc,and_comm,and_left_comm]
  have h:=(hD u u (class_mem_self D u)).1
  have hs:=card_split (classOf D u) (posNbhd G univ u)
  rw [inter_comm (classOf D u)] at hs
  rw [he]
  change _ ≤ δ*(classOf D u).card
  nlinarith

theorem negative_third_bound (δ : ℝ) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (a b : V) :
    (∑c,negativeTriple G D a b c) ≤ δ/2 := by
  have hd0:=clean_parameter_nonneg G δ D hD a
  by_cases hr:D.r a b
  · have hs:=cluster_size_pos D a
    have hrow : (∑c,negativeTriple G D a b c) ≤
        (negativeNeighbors G D b).card/(2*clusterSize D a) := by
      calc
        _ ≤ ∑c,if c∈negativeNeighbors G D b then 1/(2*clusterSize D a) else 0 := by
          apply sum_le_sum;intro c _
          unfold negativeTriple
          split_ifs with h hh hh
          · exact le_rfl
          · apply False.elim
            apply hh
            simp only [negativeNeighbors,mem_filter,mem_univ,true_and]
            exact ⟨Ne.symm h.2.2.2.2.1,h.2.2.2.2.2,D.trans (D.symm hr) h.2.1⟩
          · positivity
          · exact le_rfl
        _ = _ := by simp [←sum_filter,div_eq_mul_inv]
    have hc:=clean_negative_neighbors G δ D hD b
    rw [←cluster_size_related D hr] at hc
    exact hrow.trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith))
  · simp only [negativeTriple,hr,false_and,if_false,sum_const_zero]
    exact div_nonneg hd0 (by norm_num)

theorem negative_swap_ends (D : Setoid V) (a b c : V) :
    negativeTriple G D a b c=negativeTriple G D a c b := by
  have he : (D.r a b ∧ D.r a c ∧ G.Adj a b ∧ G.Adj a c ∧ b≠c ∧ ¬G.Adj b c) ↔
      (D.r a c ∧ D.r a b ∧ G.Adj a c ∧ G.Adj a b ∧ c≠b ∧ ¬G.Adj c b) := by
    constructor
    · intro h;exact ⟨h.2.1,h.1,h.2.2.2.1,h.2.2.1,Ne.symm h.2.2.2.2.1,fun hg=>h.2.2.2.2.2 hg.symm⟩
    · intro h;exact ⟨h.2.1,h.1,h.2.2.2.1,h.2.2.1,Ne.symm h.2.2.2.2.1,fun hg=>h.2.2.2.2.2 hg.symm⟩
  simp only [negativeTriple,he]

theorem negative_first_bound (D : Setoid V) (u v : V) :
    (∑a,negativeTriple G D a u v) ≤ (1/2:ℝ) := by
  have hs:=cluster_size_pos D u
  calc
    _ ≤ ∑a,if D.r u a then 1/(2*clusterSize D u) else 0 := by
      apply sum_le_sum;intro a _
      unfold negativeTriple
      split_ifs with h hh hh
      · rw [cluster_size_related D h.1]
      · exact False.elim (hh (D.symm h.1))
      · positivity
      · exact le_rfl
    _ = _ := by
      simp [←sum_filter,clusterSize,classOf,div_eq_mul_inv]
      have hh : ((classOf D u).card:ℝ)≠0:=ne_of_gt hs
      simp only [classOf] at hh
      field_simp [hh]

theorem negative_packing (δ : ℝ) (hd : δ ≤ 1/4) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) : IsFracPacking G (triangleMass (negativeTriple G D)) := by
  apply packing_of_triple_weights G _ (negative_triple_nonneg G D) (negative_triple_erroneous G D)
  intro u v huv
  have hm1 : (∑b,negativeTriple G D u b v)=(∑c,negativeTriple G D u v c):=sum_congr rfl (fun b _=>negative_swap_ends G D u b v)
  have hm2 : (∑b,negativeTriple G D v b u)=(∑c,negativeTriple G D v u c):=sum_congr rfl (fun b _=>negative_swap_ends G D v b u)
  rw [hm1,hm2]
  by_cases hg:G.Adj u v
  · have hz1 : (∑a,negativeTriple G D a u v)=0:=by simp [negativeTriple,hg]
    have hz2 : (∑a,negativeTriple G D a v u)=0:=by simp [negativeTriple,hg.symm]
    rw [hz1,hz2]
    linarith [negative_third_bound G δ D hD u v,negative_third_bound G δ D hD v u]
  · have hgr : ¬G.Adj v u:=fun h=>hg h.symm
    have hz1 : (∑c,negativeTriple G D u v c)=0:=by simp [negativeTriple,hg]
    have hz2 : (∑c,negativeTriple G D v u c)=0:=by simp [negativeTriple,hgr]
    rw [hz1,hz2]
    linarith [negative_first_bound G D u v,negative_first_bound G D v u]
end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem negative_empty_list :
    cutCount (fun u v : V=>u≠v ∧ ¬G.Adj u v ∧ sameCluster [] u v) univ univ=0 := by
  unfold cutCount
  apply sum_eq_zero
  intro u _
  dsimp only
  rw [filter_congr_decidable (univ : Finset V)
    (fun v=>u≠v ∧ ¬G.Adj u v ∧ sameCluster [] u v) (fun v=>Classical.propDecidable _)]
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro v _ h
  have he : u=v:=by simpa [sameCluster] using h.2.2
  exact h.1 he

theorem run_negative_ordered_bound (D : Setoid V) {R Z : Finset V}
    {L : List (Finset V × Finset V × Finset V)} (hrun : Run G R L Z) :
    cutCount (fun u v=>u≠v ∧ ¬G.Adj u v ∧ sameCluster L u v) univ univ ≤
      cutCount (IsMistake G D.r) R R := by
  induction hrun with
  | nil => rw [negative_empty_list];exact Nat.zero_le _
  | stop => rw [negative_empty_list];exact Nat.zero_le _
  | @cluster R B A L Z v hv hremove hA hne hr ih =>
    have hAR : A⊆R := by
      rw [hA]
      exact add_subset G ((removes_subset G hremove).trans (nbhd_subset G hv))
    have hclean : IsClean G R (1/4) A := by
      have hh:=run_output_clean G (Run.cluster hv hremove hA hne hr) (B,A,R) (by simp)
      norm_num [δ44] at hh
      exact hh
    have hc:=clean_internal_cost G A R hAR hclean D
    have hsum:=global_count_subadd
      (fun u w=>u≠w ∧ ¬G.Adj u w ∧ sameCluster ((B,A,R)::L) u w)
      (fun u w=>u∈A ∧ w∈A ∧ (u≠w ∧ ¬G.Adj u w))
      (fun u w=>u≠w ∧ ¬G.Adj u w ∧ sameCluster L u w) (by
        intro u w hh
        rcases hh.2.2 with he|⟨p,hp,hu,hw⟩
        · exact False.elim (hh.1 he)
        · rcases List.mem_cons.mp hp with he|hp
          · subst p;exact Or.inl ⟨hu,hw,hh.1,hh.2.1⟩
          · exact Or.inr ⟨hh.1,hh.2.1,Or.inr ⟨p,hp,hu,hw⟩⟩)
    rw [guarded_global_count] at hsum
    have hdiag:=cut_diagonal_partition_le (IsMistake G D.r) A R hAR
    omega

theorem sameCluster_symmetric (L : List (Finset V × Finset V × Finset V)) : Symmetric (sameCluster L) := by
  intro u v h
  rcases h with h|⟨p,hp,hu,hv⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨p,hp,hv,hu⟩

theorem run_negative_bound (D : Setoid V) (L : List (Finset V × Finset V × Finset V))
    (Z : Finset V) (hrun : Run G univ L Z) : negMistakes G (sameCluster L) ≤ mistakes G D.r := by
  have h:=run_negative_ordered_bound G D hrun
  have hn : cutCount (fun u v=>u≠v ∧ ¬G.Adj u v ∧ sameCluster L u v) univ univ=
      2*negMistakes G (sameCluster L) := by
    have hs : Symmetric (fun u v=>u≠v ∧ ¬G.Adj u v ∧ sameCluster L u v) := by
      intro u v h
      exact ⟨Ne.symm h.1,fun hp=>h.2.1 hp.symm,sameCluster_symmetric L h.2.2⟩
    have hh:=global_count_degree (fun u v=>u≠v ∧ ¬G.Adj u v ∧ sameCluster L u v) hs (fun v h=>h.1 rfl)
    have he : (relationPairs (fun u v=>u≠v ∧ ¬G.Adj u v ∧ sameCluster L u v)).card=
        negMistakes G (sameCluster L) := by
      unfold relationPairs negMistakes
      congr 2
    exact hh.trans (congrArg (fun x : ℕ=>2*x) he)
  have hm : cutCount (IsMistake G D.r) univ univ=2*mistakes G D.r:=mistake_degree_sum G D
  rw [hn,hm] at h
  omega

theorem lemma_twelve_exact (D : Setoid V) (L : List (Finset V × Finset V × Finset V))
    (Z : Finset V) (hrun : Run G univ L Z) : negMistakes G (sameCluster L) ≤ 4*mistakes G D.r := by
  have h:=run_negative_bound G D L Z hrun
  omega
end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def positiveCandidates (D : Setoid V) (a b : V) : Finset V :=
  univ.filter (fun c=>D.r a c ∧ G.Adj a c ∧ ¬G.Adj b c)

theorem positive_third_exact (D : Setoid V) (a b : V) (hg : G.Adj a b) (hr : ¬D.r a b) :
    (∑c,positiveTriple G D a b c)=
      (positiveCandidates G D a b).card/(clusterSize D a+clusterSize D b) := by
  simp [positiveTriple,hg,hr,positiveCandidates,←sum_filter,div_eq_mul_inv]

theorem positive_candidate_lower (δ : ℝ) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (a b : V) (hg : G.Adj a b) (hr : ¬D.r a b) :
    (1-δ)*clusterSize D a-δ*clusterSize D b ≤ (positiveCandidates G D a b).card := by
  have hsub : posNbhd G univ a∩classOf D a ⊆
      positiveCandidates G D a b ∪ (posNbhd G univ b∩(univ\classOf D b)) := by
    intro c hc
    have hac : D.r a c:=by simpa [classOf] using (mem_inter.mp hc).2
    have hbc : ¬D.r b c:=fun h=>hr (D.trans hac (D.symm h))
    by_cases hb:G.Adj b c
    · apply mem_union_right
      simp [posNbhd,classOf,hb,hbc]
    · apply mem_union_left
      have ha : G.Adj a c := by
        have hh:=(mem_inter.mp hc).1
        simp only [posNbhd,mem_insert,mem_filter,mem_univ,true_and] at hh
        rcases hh with hh|hh
        · subst c;exact False.elim (hb hg.symm)
        · exact hh
      simp [positiveCandidates,hac,ha,hb]
  have hc : ((posNbhd G univ a∩classOf D a).card:ℝ) ≤
      (positiveCandidates G D a b).card+(posNbhd G univ b∩(univ\classOf D b)).card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have ha:=(hD a a (class_mem_self D a)).1
  have hb:=(hD b b (class_mem_self D b)).2
  change (1-δ)*clusterSize D a ≤ _ at ha
  change _ ≤ δ*clusterSize D b at hb
  linarith

theorem positive_pair_mass (δ : ℝ) (hd : δ ≤ 1/4) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (a b : V) (hg : G.Adj a b) (hr : ¬D.r a b) :
    (1/2:ℝ) ≤ (∑c,positiveTriple G D a b c)+(∑c,positiveTriple G D b a c) := by
  have hrs : ¬D.r b a:=fun h=>hr (D.symm h)
  rw [positive_third_exact G D a b hg hr,positive_third_exact G D b a hg.symm hrs]
  rw [add_comm (clusterSize D b),←add_div]
  apply (le_div_iff₀ (add_pos (cluster_size_pos D a) (cluster_size_pos D b))).mpr
  have h1:=positive_candidate_lower G δ D hD a b hg hr
  have h2:=positive_candidate_lower G δ D hD b a hg.symm hrs
  nlinarith [cluster_size_pos D a,cluster_size_pos D b]

theorem positive_degree_identity (D : Setoid V) :
    cutCount (fun u v=>G.Adj u v ∧ ¬D.r u v) univ univ=2*posMistakes G D.r := by
  have hs : Symmetric (fun u v=>G.Adj u v ∧ ¬D.r u v) := by
    intro u v h;exact ⟨h.1.symm,fun hr=>h.2 (D.symm hr)⟩
  have h:=global_count_degree (fun u v=>G.Adj u v ∧ ¬D.r u v) hs (fun u h=>G.irrefl h.1)
  have he : (relationPairs (fun u v=>G.Adj u v ∧ ¬D.r u v)).card=posMistakes G D.r := by
    unfold relationPairs posMistakes
    congr 1
    ext e
    simp only [mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨u,v,he,hg,hr⟩;exact ⟨u,v,he,hg.ne,hg,hr⟩
    · rintro ⟨u,v,he,_,hg,hr⟩;exact ⟨u,v,he,hg,hr⟩
  rw [he] at h
  exact h

theorem positive_packing_mass (δ : ℝ) (hd : δ ≤ 1/4) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) :
    (posMistakes G D.r:ℝ) ≤ 2*∑T,triangleMass (positiveTriple G D) T := by
  have h : (∑a,∑b,if G.Adj a b ∧ ¬D.r a b then (1/2:ℝ) else 0) ≤
      ∑a,∑b,((∑c,positiveTriple G D a b c)+(∑c,positiveTriple G D b a c)) := by
    apply sum_le_sum;intro a _
    apply sum_le_sum;intro b _
    split_ifs with hh
    · exact positive_pair_mass G δ hd D hD a b hh.1 hh.2
    · exact add_nonneg (sum_nonneg (fun c _=>positive_triple_nonneg G D a b c))
        (sum_nonneg (fun c _=>positive_triple_nonneg G D b a c))
  have hl : (∑a,∑b,if G.Adj a b ∧ ¬D.r a b then (1/2:ℝ) else 0)=
      (cutCount (fun u v=>G.Adj u v ∧ ¬D.r u v) univ univ:ℝ)/2 := by
    simp [cutCount,←sum_filter,div_eq_mul_inv,sum_mul]
  have hs : (∑a,∑b,∑c,positiveTriple G D b a c)=(∑a,∑b,∑c,positiveTriple G D a b c):=sum_comm
  rw [hl,positive_degree_identity] at h
  simp only [sum_add_distrib,hs,Nat.cast_mul,Nat.cast_ofNat] at h
  rw [triangle_mass_total]
  linarith

theorem clean_positive_cost (δ : ℝ) (hd : δ ≤ 1/4) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (E : Setoid V) :
    posMistakes G D.r ≤ 2*mistakes G E.r := by
  have h1:=positive_packing_mass G δ hd D hD
  have h2:=packing_bound G _ (positive_packing G δ hd D hD) E
  exact_mod_cast (show (posMistakes G D.r:ℝ) ≤ 2*(mistakes G E.r:ℝ) by linarith)
end Queelius.Correlation

end

section
namespace CorrClustBBC.Cautious
theorem lemma_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (D : Setoid V) :
    ∃ D' : Setoid V, NonsingletonClean G δ D' ∧
      (mistakes G D'.r : ℝ) ≤ (9 / δ ^ 2 + 1) * (mistakes G D.r : ℝ) := by
  exact Queelius.Correlation.cleanup_all G δ hδ0 hδ1 D
end CorrClustBBC.Cautious

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem pair_mistake_split (r : V → V → Prop) (e : Sym2 V) :
    (∃u v,e=s(u,v) ∧ IsMistake G r u v) ↔
      (∃u v,e=s(u,v) ∧ u≠v ∧ G.Adj u v ∧ ¬r u v) ∨
      (∃u v,e=s(u,v) ∧ u≠v ∧ ¬G.Adj u v ∧ r u v) := by
  constructor
  · rintro ⟨u,v,he,hn,h⟩
    exact h.elim (fun h=>Or.inl ⟨u,v,he,hn,h⟩) (fun h=>Or.inr ⟨u,v,he,hn,h⟩)
  · rintro (⟨u,v,he,hn,h⟩|⟨u,v,he,hn,h⟩)
    · exact ⟨u,v,he,hn,Or.inl h⟩
    · exact ⟨u,v,he,hn,Or.inr h⟩

theorem pair_signs_conflict (r : V → V → Prop) (e : Sym2 V)
    (hp : ∃u v,e=s(u,v) ∧ u≠v ∧ G.Adj u v ∧ ¬r u v)
    (hn : ∃u v,e=s(u,v) ∧ u≠v ∧ ¬G.Adj u v ∧ r u v) : False := by
  obtain ⟨u,v,he,_,hg,_⟩:=hp
  obtain ⟨a,b,hf,_,hb,_⟩:=hn
  have h:=Sym2.eq_iff.mp (he.symm.trans hf)
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact hb hg
  · exact hb hg.symm

theorem mistakes_split (r : V → V → Prop) : mistakes G r=posMistakes G r+negMistakes G r := by
  let P : Finset (Sym2 V) := univ.filter (fun e=>∃u v,e=s(u,v) ∧ u≠v ∧ G.Adj u v ∧ ¬r u v)
  let N : Finset (Sym2 V) := univ.filter (fun e=>∃u v,e=s(u,v) ∧ u≠v ∧ ¬G.Adj u v ∧ r u v)
  let M : Finset (Sym2 V) := univ.filter (fun e=>∃u v,e=s(u,v) ∧ IsMistake G r u v)
  have hM : M=P∪N := by
    ext e
    simp only [M,P,N,mem_filter,mem_univ,true_and,mem_union,pair_mistake_split G r]
  have hd : Disjoint P N := by
    apply disjoint_left.mpr
    intro e hp hn
    exact pair_signs_conflict G r e (mem_filter.mp hp).2 (mem_filter.mp hn).2
  have hm : mistakes G r=M.card := by unfold mistakes M;congr 2
  have hp : posMistakes G r=P.card := by unfold posMistakes P;congr 2
  have hn : negMistakes G r=N.card := by unfold negMistakes N;congr 2
  rw [hm,hp,hn]
  calc
    _ = (P∪N).card := congrArg Finset.card hM
    _ = _ := card_union_of_disjoint hd

theorem root_from_negative_bound
    (hneg : ∀ (L : List (Finset V × Finset V × Finset V)) (Z : Finset V),
      Run G univ L Z → ∀D:Setoid V,negMistakes G (sameCluster L) ≤ 4*mistakes G D.r) :
    (∃L Z,Run G univ L Z) ∧
      ∀ (L : List (Finset V × Finset V × Finset V)) (Z : Finset V),Run G univ L Z →
        ∀D:Setoid V,(mistakes G (sameCluster L):ℝ) ≤ (9/δ44^2+5)*(mistakes G D.r:ℝ) := by
  refine ⟨run_exists G univ,?_⟩
  intro L Z hr D
  obtain ⟨D',hclean,hcost⟩:=cleanup_all G δ44 (by norm_num [δ44]) (by norm_num [δ44]) D
  have hp:=positive_mistakes_bound G D' hclean L Z hr
  have hneg:=hneg L Z hr D
  have hcomp : posMistakes G D'.r ≤ mistakes G D'.r := by rw [mistakes_split];omega
  have hpos : (posMistakes G (sameCluster L):ℝ) ≤ mistakes G D'.r := by exact_mod_cast hp.trans hcomp
  have hn : (negMistakes G (sameCluster L):ℝ) ≤ 4*(mistakes G D.r:ℝ) := by exact_mod_cast hneg
  rw [mistakes_split,Nat.cast_add]
  linarith
theorem root_exact :
    (∃L Z,Run G univ L Z) ∧
      ∀ (L : List (Finset V × Finset V × Finset V)) (Z : Finset V),Run G univ L Z →
        ∀D:Setoid V,(mistakes G (sameCluster L):ℝ) ≤ (9/δ44^2+5)*(mistakes G D.r:ℝ) :=
  root_from_negative_bound G (fun L Z hr D=>lemma_twelve_exact G D L Z hr)
end Queelius.Correlation

end

section
noncomputable section
namespace Queelius.Correlation.Controls
open Finset Classical CorrClustBBC.Cautious

theorem cut_count_eval {V : Type*} [DecidableEq V] (Q : V→V→Prop) [DecidableRel Q]
    (A B : Finset V) : cutCount Q A B=∑u∈A,(B.filter (Q u)).card := by
  unfold cutCount
  apply sum_congr rfl
  intro u _
  apply congrArg Finset.card
  exact filter_congr_decidable B (Q u) (fun v=>Classical.propDecidable _)

def cycleFour : SimpleGraph (Fin 4) where
  Adj u v := u.val%2≠v.val%2
  symm := ⟨by intro u v h;exact Ne.symm h⟩
  loopless := ⟨by intro u h;exact h rfl⟩
instance : DecidableRel cycleFour.Adj := fun u v=>inferInstanceAs (Decidable (u.val%2≠v.val%2))

def halves : Setoid (Fin 4):=Setoid.ker (fun u : Fin 4=>u.val/2)
instance : DecidableRel halves.r := fun u v=>inferInstanceAs (Decidable (u.val/2=v.val/2))
instance mistakeDecidable (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] : DecidableRel (IsMistake G halves.r) := by
  intro u v
  unfold IsMistake
  infer_instance

theorem cycle_quarter_clean : IsClean cycleFour univ (1/4) univ := by
  intro u _
  have hc : (posNbhd cycleFour univ u).card=3 := by fin_cases u <;> decide
  simp only [IsGood,inter_univ,sdiff_self,bot_eq_empty,inter_empty,card_empty,Nat.cast_zero,card_univ,Fintype.card_fin]
  rw [hc]
  norm_num

theorem cycle_negative_row (u : Fin 4) :
    (univ.filter (fun v=>u≠v ∧ ¬cycleFour.Adj u v)).card=1 := by fin_cases u <;> decide

theorem cycle_comparison_row (u : Fin 4) :
    (univ.filter (IsMistake cycleFour halves.r u)).card=1 := by fin_cases u <;> decide

theorem internal_bound_sharp :
    cutCount (fun u v : Fin 4=>u≠v ∧ ¬cycleFour.Adj u v) univ univ=4 ∧
    cutCount (IsMistake cycleFour halves.r) univ univ=4 := by
  constructor
  · simp [cutCount,cycle_negative_row]
  · rw [cut_count_eval];simp [cycle_comparison_row]

def twoEdges : SimpleGraph (Fin 4) where
  Adj u v := u≠v ∧ u.val/2=v.val/2
  symm := ⟨by intro u v h;exact ⟨Ne.symm h.1,h.2.symm⟩⟩
  loopless := ⟨by intro u h;exact h.1 rfl⟩
instance : DecidableRel twoEdges.Adj := fun u v=>inferInstanceAs (Decidable (u≠v ∧ u.val/2=v.val/2))

theorem half_clean_does_not_suffice :
    IsClean twoEdges univ (1/2) univ ∧
    cutCount (fun u v : Fin 4=>u≠v ∧ ¬twoEdges.Adj u v) univ univ=8 ∧
    cutCount (IsMistake twoEdges halves.r) univ univ=0 := by
  have hdeg (u : Fin 4) : (posNbhd twoEdges univ u).card=2 := by fin_cases u <;> decide
  have hn (u : Fin 4) : (univ.filter (fun v=>u≠v ∧ ¬twoEdges.Adj u v)).card=2 := by fin_cases u <;> decide
  have hm (u : Fin 4) : (univ.filter (IsMistake twoEdges halves.r u)).card=0 := by fin_cases u <;> decide
  refine ⟨?_,?_,?_⟩
  · intro u _
    simp only [IsGood,inter_univ,sdiff_self,bot_eq_empty,inter_empty,card_empty,Nat.cast_zero,card_univ,Fintype.card_fin]
    rw [hdeg]
    norm_num
  · simp [cutCount,hn]
  · rw [cut_count_eval];simp [hm]
end Queelius.Correlation.Controls

end

section
namespace CorrClustBBC.Cautious
theorem lemma_12 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : List (Finset V × Finset V × Finset V)) (Z : Finset V) (hrun : Run G Finset.univ L Z)
    (D : Setoid V) :
    negMistakes G (sameCluster L) ≤ 4 * mistakes G D.r := by
  exact Queelius.Correlation.lemma_twelve_exact G D L Z hrun
end CorrClustBBC.Cautious

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem within_class_sum (Q : V→V→Prop) (D : Setoid V) :
    (∑C∈clusterFamily D,(cutCount Q C C:ℝ))=
      (cutCount (fun u v=>Q u v ∧ D.r u v) univ univ:ℝ) := by
  have he (C : Finset V) (hC : C∈clusterFamily D) :
      (cutCount Q C C:ℝ)=∑u∈C,((univ.filter (fun v=>Q u v ∧ D.r u v)).card:ℝ) := by
    simp only [cutCount,Nat.cast_sum]
    apply sum_congr rfl
    intro u hu
    have hc:=class_at_member D C hC u hu
    apply congrArg (fun S : Finset V=>(S.card:ℝ))
    ext v
    rw [←hc]
    simp [classOf,and_comm]
  calc
    _ = ∑C∈clusterFamily D,∑u∈C,((univ.filter (fun v=>Q u v ∧ D.r u v)).card:ℝ) := sum_congr rfl he
    _ = ∑u,((univ.filter (fun v=>Q u v ∧ D.r u v)).card:ℝ) := sum_over_classes D _
    _ = _ := by simp [cutCount]

variable (G : SimpleGraph V) [DecidableRel G.Adj]
theorem negative_degree_identity (D : Setoid V) :
    cutCount (fun u v=>u≠v ∧ ¬G.Adj u v ∧ D.r u v) univ univ=2*negMistakes G D.r := by
  have hs : Symmetric (fun u v=>u≠v ∧ ¬G.Adj u v ∧ D.r u v) := by
    intro u v h;exact ⟨Ne.symm h.1,fun hp=>h.2.1 hp.symm,D.symm h.2.2⟩
  have hh:=global_count_degree (fun u v=>u≠v ∧ ¬G.Adj u v ∧ D.r u v) hs (fun v h=>h.1 rfl)
  have he : (relationPairs (fun u v=>u≠v ∧ ¬G.Adj u v ∧ D.r u v)).card=negMistakes G D.r:=by
    unfold relationPairs negMistakes
    congr 2
  exact hh.trans (congrArg (fun n : ℕ=>2*n) he)

theorem clean_negative_cost (δ : ℝ) (hd : δ ≤ 1/4) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (E : Setoid V) :
    negMistakes G D.r ≤ mistakes G E.r := by
  have hc (C : Finset V) (hC : C∈clusterFamily D) : IsClean G univ (1/4) C := by
    obtain ⟨v,_,rfl⟩:=mem_image.mp hC
    intro u hu
    have h:=hD v u hu
    have hm:=mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (α:=ℝ) (classOf D v).card)
    constructor <;> nlinarith [h.1,h.2]
  have hb : (∑C∈clusterFamily D,(cutCount (fun u v=>u≠v ∧ ¬G.Adj u v) C C:ℝ)) ≤
      ∑C∈clusterFamily D,(cutCount (IsMistake G E.r) C C:ℝ) := by
    apply sum_le_sum;intro C hC
    exact_mod_cast clean_internal_cost G C univ (subset_univ _) (hc C hC) E
  rw [within_class_sum,within_class_sum] at hb
  have hm : cutCount (fun u v=>IsMistake G E.r u v ∧ D.r u v) univ univ ≤
      cutCount (IsMistake G E.r) univ univ := by
    apply sum_le_sum;intro u _
    apply card_le_card
    intro v hv
    simp only [mem_filter,mem_univ,true_and] at hv ⊢
    exact hv.1
  have he : cutCount (fun u v=>(u≠v ∧ ¬G.Adj u v) ∧ D.r u v) univ univ=
      cutCount (fun u v=>u≠v ∧ ¬G.Adj u v ∧ D.r u v) univ univ := by
    congr 1;funext u v;exact propext and_assoc
  rw [he,negative_degree_identity] at hb
  have hmr : (cutCount (IsMistake G E.r) univ univ:ℝ)=2*(mistakes G E.r:ℝ) := by
    exact_mod_cast mistake_degree_sum G E
  have hmc : (cutCount (fun u v=>IsMistake G E.r u v ∧ D.r u v) univ univ:ℝ) ≤
      cutCount (IsMistake G E.r) univ univ:=by exact_mod_cast hm
  rw [hmr] at hmc
  push_cast at hb
  exact_mod_cast (show (negMistakes G D.r:ℝ) ≤ mistakes G E.r by linarith)

theorem clean_comparison_three (δ : ℝ) (hd : δ ≤ 1/4) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (E : Setoid V) :
    mistakes G D.r ≤ 3*mistakes G E.r := by
  have hp:=clean_positive_cost G δ hd D hD E
  have hn:=clean_negative_cost G δ hd D hD E
  rw [mistakes_split]
  omega

theorem clean_corollary_five (δ : ℝ) (hd : δ ≤ 1/4) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (E : Setoid V) :
    mistakes G D.r ≤ 4*mistakes G E.r := by
  have h:=clean_comparison_three G δ hd D hD E
  omega
end Queelius.Correlation

end

section
universe audit_u0
theorem solution : (
∀ {V : Type audit_u0} [inst : Fintype V] [inst_1 : DecidableEq V] (G : SimpleGraph V)
  [inst_2 : @DecidableRel V V (@SimpleGraph.Adj V G)],
  And
    (@Exists (List (Prod (Finset V) (Prod (Finset V) (Finset V))))
      fun (L : List (Prod (Finset V) (Prod (Finset V) (Finset V)))) =>
      @Exists (Finset V) fun (Z : Finset V) =>
        @CorrClustBBC.Cautious.Run V inst inst_1 G inst_2 (@Finset.univ V inst) L Z)
    (∀ (L : List (Prod (Finset V) (Prod (Finset V) (Finset V)))) (Z : Finset V),
      @CorrClustBBC.Cautious.Run V inst inst_1 G inst_2 (@Finset.univ V inst) L Z →
        ∀ (D : Setoid V),
          @LE.le Real Real.instLE
            (@Nat.cast Real Real.instNatCast
              (@CorrClustBBC.Cautious.mistakes V inst inst_1 G (@CorrClustBBC.Cautious.sameCluster V L)))
            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
              (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                  (@OfNat.ofNat Real (nat_lit 9)
                    (@instOfNatAtLeastTwo Real (nat_lit 9) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                  (@HPow.hPow Real Nat Real
                    (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                    CorrClustBBC.Cautious.δ44 (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@OfNat.ofNat Real (nat_lit 5)
                  (@instOfNatAtLeastTwo Real (nat_lit 5) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
              (@Nat.cast Real Real.instNatCast (@CorrClustBBC.Cautious.mistakes V inst inst_1 G (@Setoid.r V D)))))
) := @Queelius.Correlation.root_exact

end

section
noncomputable section
namespace Queelius.Correlation
open Finset Classical CorrClustBBC.Cautious
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def negativeCandidates (D : Setoid V) (u v : V) : Finset V :=
  univ.filter (fun a=>D.r u a ∧ G.Adj a u ∧ G.Adj a v)

theorem negative_first_exact (D : Setoid V) (u v : V) (hne : u≠v)
    (hg : ¬G.Adj u v) (hr : D.r u v) :
    (∑a,negativeTriple G D a u v)=(negativeCandidates G D u v).card/(2*clusterSize D u) := by
  calc
    _ = ∑a,if D.r u a ∧ G.Adj a u ∧ G.Adj a v then 1/(2*clusterSize D u) else 0 := by
      apply sum_congr rfl;intro a _
      by_cases h:D.r u a ∧ G.Adj a u ∧ G.Adj a v
      · have hau:=D.symm h.1
        have hav:=D.trans hau hr
        simp [negativeTriple,hau,hav,h.1,h.2.1,h.2.2,hne,hg,cluster_size_related D hau]
      · have hh : ¬(D.r a u ∧ D.r a v ∧ G.Adj a u ∧ G.Adj a v ∧ u≠v ∧ ¬G.Adj u v) := by
          intro hh;exact h ⟨D.symm hh.1,hh.2.2.1,hh.2.2.2.1⟩
        simp [negativeTriple,hh,h]
    _ = _ := by simp [←sum_filter,negativeCandidates,div_eq_mul_inv]

theorem negative_candidate_lower (δ : ℝ) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (u v : V) (hne : u≠v)
    (hg : ¬G.Adj u v) (hr : D.r u v) :
    (1-2*δ)*clusterSize D u ≤ (negativeCandidates G D u v).card := by
  let A:=posNbhd G univ u∩classOf D u
  let B:=posNbhd G univ v∩classOf D u
  have hsub : A∪B⊆classOf D u:=union_subset inter_subset_right inter_subset_right
  have he : A∩B=negativeCandidates G D u v := by
    ext a
    simp only [A,B,negativeCandidates,mem_inter,mem_filter,mem_univ,true_and,classOf,posNbhd,mem_insert]
    constructor
    · rintro ⟨⟨ha,hr1⟩,hb,hr2⟩
      have hau : G.Adj a u := by
        rcases ha with ha|ha
        · subst a
          rcases hb with hb|hb
          · exact False.elim (hne hb)
          · exact False.elim (hg hb.symm)
        · exact ha.symm
      have hav : G.Adj a v := by
        rcases hb with hb|hb
        · subst a
          exact False.elim (hg hau.symm)
        · exact hb.symm
      exact ⟨hr1,hau,hav⟩
    · intro h;exact ⟨⟨Or.inr h.2.1.symm,h.1⟩,Or.inr h.2.2.symm,h.1⟩
  have hc : (A.card:ℝ)+(B.card:ℝ) ≤ clusterSize D u+(negativeCandidates G D u v).card := by
    have hh:=card_union_add_card_inter A B
    have hs:=card_le_card hsub
    rw [he] at hh
    unfold clusterSize
    exact_mod_cast (show A.card+B.card ≤ (classOf D u).card+(negativeCandidates G D u v).card by omega)
  have hu:=(hD u u (class_mem_self D u)).1
  have hv:=(hD v v (class_mem_self D v)).1
  rw [←class_eq_of_related D hr] at hv
  change (1-δ)*clusterSize D u ≤ (A.card:ℝ) at hu
  change (1-δ)*clusterSize D u ≤ (B.card:ℝ) at hv
  nlinarith

theorem negative_pair_mass (δ : ℝ) (hd : δ ≤ 1/4) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) (u v : V) (hne : u≠v)
    (hg : ¬G.Adj u v) (hr : D.r u v) :
    (1/4:ℝ) ≤ ∑a,negativeTriple G D a u v := by
  rw [negative_first_exact G D u v hne hg hr]
  apply (le_div_iff₀ (mul_pos (by norm_num) (cluster_size_pos D u))).mpr
  have h:=negative_candidate_lower G δ D hD u v hne hg hr
  nlinarith [cluster_size_pos D u]

theorem negative_packing_mass (δ : ℝ) (hd : δ ≤ 1/4) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) :
    (negMistakes G D.r:ℝ) ≤ 2*∑T,triangleMass (negativeTriple G D) T := by
  have h : (∑u,∑v,if u≠v ∧ ¬G.Adj u v ∧ D.r u v then (1/4:ℝ) else 0) ≤
      ∑u,∑v,∑a,negativeTriple G D a u v := by
    apply sum_le_sum;intro u _
    apply sum_le_sum;intro v _
    split_ifs with hh
    · exact negative_pair_mass G δ hd D hD u v hh.1 hh.2.1 hh.2.2
    · exact sum_nonneg (fun a _=>negative_triple_nonneg G D a u v)
  have hl : (∑u,∑v,if u≠v ∧ ¬G.Adj u v ∧ D.r u v then (1/4:ℝ) else 0)=
      (cutCount (fun u v=>u≠v ∧ ¬G.Adj u v ∧ D.r u v) univ univ:ℝ)/4 := by
    simp [cutCount,←sum_filter,div_eq_mul_inv,sum_mul]
  have hs : (∑u,∑v,∑a,negativeTriple G D a u v)=(∑a,∑u,∑v,negativeTriple G D a u v) := by
    conv_lhs => arg 2;ext u;rw [sum_comm]
    rw [sum_comm]
  rw [hl,negative_degree_identity] at h
  simp only [hs,Nat.cast_mul,Nat.cast_ofNat] at h
  rw [triangle_mass_total]
  linarith

theorem clean_packing_four (δ : ℝ) (hd : δ ≤ 1/4) (D : Setoid V)
    (hD : ∀ u,IsClean G univ δ (classOf D u)) :
    ∃ w : Finset V→ℝ,IsFracPacking G w ∧ (mistakes G D.r:ℝ) ≤ 4*∑T,w T := by
  by_cases h:negMistakes G D.r ≤ posMistakes G D.r
  · refine ⟨triangleMass (positiveTriple G D),positive_packing G δ hd D hD,?_⟩
    have hm:=positive_packing_mass G δ hd D hD
    have hh : (negMistakes G D.r:ℝ) ≤ posMistakes G D.r:=by exact_mod_cast h
    rw [mistakes_split,Nat.cast_add]
    linarith
  · refine ⟨triangleMass (negativeTriple G D),negative_packing G δ hd D hD,?_⟩
    have hm:=negative_packing_mass G δ hd D hD
    have hh : (posMistakes G D.r:ℝ) ≤ negMistakes G D.r:=by exact_mod_cast (le_of_not_ge h)
    rw [mistakes_split,Nat.cast_add]
    linarith
end Queelius.Correlation

end

section
namespace CorrClustBBC.Cautious
theorem lemma_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (δ : ℝ) (hδ : δ ≤ 1 / 4) (D : Setoid V)
    (hD : ∀ v, IsClean G Finset.univ δ (classOf D v)) :
    ∃ w : Finset V → ℝ, IsFracPacking G w ∧ (mistakes G D.r : ℝ) ≤ 4 * ∑ T, w T := by
  exact Queelius.Correlation.clean_packing_four G δ hδ D hD
end CorrClustBBC.Cautious

namespace CorrClustBBC.Cautious
theorem corollary_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (δ : ℝ) (hδ : δ ≤ 1 / 4) (D : Setoid V)
    (hD : ∀ v, IsClean G Finset.univ δ (classOf D v)) (D' : Setoid V) :
    mistakes G D.r ≤ 4 * mistakes G D'.r := by
  exact Queelius.Correlation.clean_corollary_five G δ hδ D hD D'
end CorrClustBBC.Cautious


end

section
noncomputable section
namespace Queelius.Correlation.Controls
open Finset Classical CorrClustBBC.Cautious
set_option maxHeartbeats 4000000

theorem cycle_negative_packing_mass :
    IsFracPacking cycleFour (triangleMass (negativeTriple cycleFour (⊤ : Setoid (Fin 4)))) ∧
    (∑T,triangleMass (negativeTriple cycleFour (⊤ : Setoid (Fin 4))) T)=1 := by
  constructor
  · apply negative_packing cycleFour (1/4) le_rfl
    intro u
    have hc : classOf (⊤ : Setoid (Fin 4)) u=univ := by ext v;simp [classOf]
    rw [hc]
    exact cycle_quarter_clean
  · rw [triangle_mass_total]
    let P:=fun a b c : Fin 4=>cycleFour.Adj a b ∧ cycleFour.Adj a c ∧ b≠c ∧ ¬cycleFour.Adj b c
    have hc : (∑a,∑b,∑c,if P a b c then (1:ℕ) else 0)=8 := by decide
    have hr : (∑a,∑b,∑c,if P a b c then (1:ℝ) else 0)=8 := by exact_mod_cast hc
    have hs (a : Fin 4) : clusterSize (⊤ : Setoid (Fin 4)) a=4:=by simp [clusterSize,classOf]
    have he (a b c : Fin 4) : negativeTriple cycleFour (⊤ : Setoid (Fin 4)) a b c=
        if P a b c then (1/8:ℝ) else 0 := by norm_num [negativeTriple,hs,P]
    simp_rw [he]
    calc
      _ = (∑a,∑b,∑c,if P a b c then (1:ℝ) else 0)/8 := by simp only [sum_div,ite_div,zero_div]
      _ = 1 := by rw [hr];norm_num

def cliqueMatching : SimpleGraph (Fin 8) where
  Adj u v := u≠v ∧ (u.val/4=v.val/4 ∨ u.val%4=v.val%4)
  symm := ⟨by intro u v h;exact ⟨Ne.symm h.1,h.2.elim (fun h=>Or.inl h.symm) (fun h=>Or.inr h.symm)⟩⟩
  loopless := ⟨by intro u h;exact h.1 rfl⟩
instance cliqueMatchingDecidable : DecidableRel cliqueMatching.Adj:=fun u v=>inferInstanceAs (Decidable (u≠v ∧ (u.val/4=v.val/4 ∨ u.val%4=v.val%4)))
def blocksFour : Setoid (Fin 8):=Setoid.ker (fun u : Fin 8=>u.val/4)

instance blocksFourDecidable : DecidableRel blocksFour.r:=fun u v=>inferInstanceAs (Decidable (u.val/4=v.val/4))

def blockFour (u : Fin 8) : Finset (Fin 8):=univ.filter (fun v=>u.val/4=v.val/4)
@[simp] theorem blocks_relation (u v : Fin 8) : blocksFour.r u v ↔ u.val/4=v.val/4:=Iff.rfl
@[simp] theorem blocks_class (u : Fin 8) : classOf blocksFour u=blockFour u := by
  ext v;simp [classOf,blockFour]
@[simp] theorem block_card (u : Fin 8) : (blockFour u).card=4 := by fin_cases u <;> decide

theorem matching_clean : ∀ u,IsClean cliqueMatching univ (1/4) (classOf blocksFour u) := by
  have rows : ∀ u v : Fin 8,v∈blockFour u →
      (posNbhd cliqueMatching univ v∩blockFour u).card=4 ∧
      (posNbhd cliqueMatching univ v∩(univ\blockFour u)).card=1 := by decide
  intro u
  rw [blocks_class]
  intro v hv
  obtain ⟨hi,he⟩:=rows u v hv
  unfold IsGood
  rw [hi,he,block_card]
  norm_num

theorem matching_positive_packing_mass :
    IsFracPacking cliqueMatching (triangleMass (positiveTriple cliqueMatching blocksFour)) ∧
    (∑T,triangleMass (positiveTriple cliqueMatching blocksFour) T)=3 := by
  constructor
  · exact positive_packing cliqueMatching (1/4) le_rfl blocksFour matching_clean
  · rw [triangle_mass_total]
    let P:=fun a b c : Fin 8=>cliqueMatching.Adj a b ∧ ¬blocksFour.r a b ∧ blocksFour.r a c ∧ cliqueMatching.Adj a c ∧ ¬cliqueMatching.Adj b c
    have hc : (∑a,∑b,∑c,if P a b c then (1:ℕ) else 0)=24 := by decide
    have hr : (∑a,∑b,∑c,if P a b c then (1:ℝ) else 0)=24 := by exact_mod_cast hc
    have he (a b c : Fin 8) : positiveTriple cliqueMatching blocksFour a b c=
        if P a b c then (1/8:ℝ) else 0 := by
      simp only [positiveTriple,clusterSize,blocks_class,block_card]
      norm_num only [Nat.cast_ofNat,show (4:ℝ)+4=8 by norm_num]
      rfl
    simp_rw [he]
    calc
      _ = (∑a,∑b,∑c,if P a b c then (1:ℝ) else 0)/8 := by simp only [sum_div,ite_div,zero_div]
      _ = 3 := by rw [hr];norm_num

end Queelius.Correlation.Controls

end
