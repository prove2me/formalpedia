-- Prove2me | solution 1 for Freiman.trunk_bindings_08_200_262
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:28:46.231965+00:00
-- url     : https://prove2.me/submissions/cfaa1378-b330-40c1-bdb5-cf939c94296e

import Definitions.Def_Freiman_trunkFast
import Theorems.Thm_Freiman_trunkFast_correctness
open Freiman Freiman.TrunkFast
private def intCode (z : ℤ) : ℕ := if z < 0 then 2*z.natAbs+1 else 2*z.natAbs
private def proj (b : CertBound) : ℕ :=
  [b.lower.toNat,b.strict.toNat,intCode b.threshold.c.a.num,b.threshold.c.a.den,
   intCode b.threshold.x0.a.num,b.threshold.x0.a.den,intCode b.threshold.c.b.num,
   b.threshold.c.b.den,intCode b.threshold.x0.b.num,b.threshold.x0.b.den].foldl
    (fun acc n => ((acc+n+17)*(acc+n+17)+3*acc) % 1000000007) 7
private def fingerprint (bs : List CertBound) : ℕ := ((bs.map proj).toFinset.sum id)

private theorem fingerprint_congr {cs bs : List CertBound} (heq : cs.toFinset = bs.toFinset) :
    fingerprint cs = fingerprint bs := by
  have hm : ∀ b, b ∈ cs ↔ b ∈ bs := by
    intro b
    have h := congrArg (fun s : Finset CertBound => b ∈ s) heq
    simpa using Iff.of_eq h
  have hi : (cs.map proj).toFinset = (bs.map proj).toFinset := by
    ext z
    simp only [List.mem_toFinset,List.mem_map,hm]
  exact congrArg (fun s : Finset ℕ => s.sum id) hi
private theorem parents_of_fingerprints (raw : List (List CertBound))
    (h : (raw.map fingerprint).Nodup) : raw.Pairwise (fun cs bs => cs.toFinset ≠ bs.toFinset) := by
  have h' : raw.Pairwise (fun cs bs => fingerprint cs ≠ fingerprint bs) := List.pairwise_map.mp h
  exact h'.imp fun hne heq => hne (fingerprint_congr heq)

private def fprints8 : List ℕ := [4325838231, 4163376800, 4425776615, 4417291780, 4165885676, 5317814407, 5155352976, 5417752791, 5409267956, 5157861852, 3714549947, 3552088516, 3814488331, 3806003496, 3554597392, 4706526123, 4544064692, 4806464507, 4797979672, 4546573568, 4499614243, 4337152812, 4599552627, 4591067792, 4339661688, 5491590419, 5329128988, 5591528803, 5583043968, 5331637864, 3695453821, 3532992390, 3795392205, 3786907370, 3535501266, 4687429997, 4524968566, 4787368381, 4778883546, 4527477442, 4850989863, 4688528432, 4950928247, 4942443412, 4691037308, 3968267512, 3805806081, 4068205896, 4059721061, 3808314957, 5763869542, 5601408111, 5863807926, 5855323091, 4762114077, 6755845718, 6593384287, 6855784102, 6847299267, 5754090253, 5152581258, 4990119827, 5252519642, 5244034807, 4150825793, 6144557434, 5982096003, 6244495818, 6236010983, 5142801969, 5937645554, 5775184123, 6037583938, 6029099103, 4935890089, 6929621730, 6767160299, 7029560114, 7021075279, 5927866265, 5133485132, 4971023701, 5233423516, 5224938681, 4131729667, 6125461308, 5962999877, 6225399692, 6216914857, 5123705843, 6289021174, 6126559743, 6388959558, 6380474723, 5287265709, 5406298823, 5243837392, 5506237207, 5497752372, 4404543358, 5452433595, 5289972164, 5552371979, 5543887144, 4450678130, 6444409771, 6281948340, 6544348155, 6535863320, 5442654306, 4889340785, 4726879354, 4989279169, 4980794334, 3887585320, 5881316961, 5718855530, 5981255345, 5972770510, 4879561496, 5626209607, 5463748176, 5726147991, 5717663156, 4624454142, 6618185783, 6455724352, 6718124167, 6709639332, 5616430318, 5586827744, 5424366313, 5686766128, 5678281293, 4585072279, 6578803920, 6416342489, 6678742304, 6670257469, 5577048455, 5977585227, 5815123796, 6077523611, 6069038776, 4975829762, 5094862876, 4932401445, 5194801260, 5186316425, 4093107411, 6413071998, 6250610567, 6513010382, 6504525547, 5411316533, 7405048174, 7242586743, 7504986558, 7496501723, 6403292709, 5801783714, 5639322283, 5901722098, 5893237263, 4800028249, 6793759890, 6631298459, 6893698274, 6885213439, 5792004425, 6586848010, 6424386579, 6686786394, 6678301559, 5585092545, 7578824186, 7416362755, 7678762570, 7670277735, 6577068721, 5782687588, 5620226157, 5882625972, 5874141137, 4780932123, 6774663764, 6612202333, 6874602148, 6866117313, 5772908299, 6938223630, 6775762199, 7038162014, 7029677179, 5936468165, 6055501279, 5893039848, 6155439663, 6146954828, 5053745814, 5250137420, 5087675989, 5350075804, 5341590969, 4248381955, 6242113596, 6079652165, 6342051980, 6333567145, 5240358131, 5206499587, 5044038156, 5306437971, 5297953136, 4204744122, 6198475763, 6036014332, 6298414147, 6289929312, 5196720298, 5423913432, 5261452001, 5523851816, 5515366981, 4422157967, 6415889608, 6253428177, 6515827992, 6507343157, 5414134143, 4979276577, 4816815146, 5079214961, 5070730126, 3977521112, 5971252753, 5808791322, 6071191137, 6062706302, 4969497288, 5775289052, 5612827621, 5875227436, 5866742601, 4773533587, 4892566701, 4730105270, 4992505085, 4984020250, 3890811236]
private theorem hprints8 : (trunkRawParents (trunkCatalog.states 8).context).map fingerprint = fprints8 := by
  decide +kernel
private theorem hPar8 : trunkParents (trunkCatalog.states 8).context = trunkRawParents (trunkCatalog.states 8).context := by
  apply Freiman.trunkFast_correctness.1
  apply parents_of_fingerprints
  rw [hprints8]
  decide +kernel

theorem batch_chunk_0 : ∀ j ∈ List.range 20, trunkGroupValidFast 8 (trunkStateData08Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold trunkGroupValidFast trunkResidualFast
  decide +kernel

theorem batch_chunk_20 : ∀ j ∈ List.range' 20 20, trunkGroupValidFast 8 (trunkStateData08Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold trunkGroupValidFast trunkResidualFast
  decide +kernel

theorem batch_chunk_40 : ∀ j ∈ List.range' 40 20, trunkGroupValidFast 8 (trunkStateData08Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold trunkGroupValidFast trunkResidualFast
  decide +kernel

theorem batch_chunk_60 : ∀ j ∈ List.range' 60 2, trunkGroupValidFast 8 (trunkStateData08Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold trunkGroupValidFast trunkResidualFast
  decide +kernel

theorem batch_key (j : ℕ) (hj : j < 62) : trunkGroupValidFast 8 (trunkStateData08Part03.getD j ⟨0,[],0,[]⟩) := by
  rcases lt_or_ge j 20 with h0 | h0
  · exact batch_chunk_0 j (List.mem_range.2 (by omega))
  rcases lt_or_ge j 40 with h1 | h1
  · exact batch_chunk_20 j (List.mem_range'.2 ⟨j - 20, by omega, by omega⟩)
  rcases lt_or_ge j 60 with h2 | h2
  · exact batch_chunk_40 j (List.mem_range'.2 ⟨j - 40, by omega, by omega⟩)
  · exact batch_chunk_60 j (List.mem_range'.2 ⟨j - 60, by omega, by omega⟩)

theorem part_length_1 : trunkStateData08Part01.length = 100 := by decide +kernel

theorem part_length_2 : trunkStateData08Part02.length = 100 := by decide +kernel

theorem solution : trunkBindingBatch 8 200 262 := by
  intro i hlo hhi g hg
  change (trunkStateData08Part01 ++ trunkStateData08Part02 ++ trunkStateData08Part03)[i]? = some g at hg
  rw [List.getElem?_append_right (show (trunkStateData08Part01 ++ trunkStateData08Part02).length ≤ i by simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd]; omega)] at hg
  simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd] at hg
  have hgi := batch_key (i - 200) (by omega)
  have hgv : trunkStateData08Part03.getD (i - 200) ⟨0,[],0,[]⟩ = g := by
    try simp only [Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hgv] at hgi
  exact Freiman.trunkFast_correctness.2 8 hPar8 g hgi

#print axioms solution
